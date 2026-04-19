import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
import threading
import time
import asyncio
import json
import os
import csv
from collections import deque
import abc
import re
from typing import Optional, Tuple, cast

# --- 模組載入處理 ---
try:
    import serial
    HAS_SERIAL = True
except ImportError:
    HAS_SERIAL = False

# 防止 Bleak 載入失敗導致程式崩潰
BleakScanner, BleakClient = None, None
try:
    from bleak import BleakScanner, BleakClient
    HAS_BLE = True
except Exception:
    HAS_BLE = False

try:
    import requests
    import socketio
    HAS_SOCKETIO = True
except ImportError:
    HAS_SOCKETIO = False

# HM-10 BLE UUID
UART_SERVICE_UUID = "0000ffe0-0000-1000-8000-00805f9b34fb"
UART_CHAR_UUID    = "0000ffe1-0000-1000-8000-00805f9b34fb"

# ==========================================
# 計分板類別 (Scoreboard)
# ==========================================
class Scoreboard(abc.ABC):
    def __init__(self, gui_log=None):
        self.gui_log = gui_log
    def log_msg(self, msg, t="SYS"):
        if self.gui_log: self.gui_log(str(msg), t)
    @abc.abstractmethod
    def add_UID(self, UID_str: str) -> Tuple[int, float]: pass
    @abc.abstractmethod
    def get_current_score(self) -> Optional[int]: pass

class ScoreboardFake(Scoreboard):
    def __init__(self, teamname, filepath, gui_log=None):
        super().__init__(gui_log)
        self.total_score = 0
        self.uid_to_score = {}
        try:
            with open(filepath, "r", encoding="utf-8-sig") as f:
                reader = csv.reader(f)
                rows = list(reader)
                for row in rows[1:]:
                    if len(row) >= 2:
                        # 強制轉大寫並去除空白，防止 CSV 格式誤差
                        self.uid_to_score[row[0].strip().upper()] = int(row[1].strip())
            self.log_msg(f"本地 Fake 計分板載入成功 ({len(self.uid_to_score)} 筆資料)")
        except Exception as e: 
            self.log_msg(f"讀取 Fake CSV 失敗: {e}", "ERR")
        self.visit_list = set()

    def add_UID(self, UID_str: str):
        # 比對時也強制轉大寫與去除空白
        UID_str = UID_str.strip().upper()
        if UID_str in self.uid_to_score and UID_str not in self.visit_list:
            point = self.uid_to_score[UID_str]
            self.total_score += point
            self.visit_list.add(UID_str)
            self.log_msg(f"尋獲寶藏！獲得 {point} 分")
            return point, 0
        return 0, 0
    def get_current_score(self): return int(self.total_score)

if HAS_SOCKETIO:
    class TeamNamespace(socketio.ClientNamespace):
        def __init__(self, ns, gui_log):
            super().__init__(ns)
            self.gui_log = gui_log
        def on_connect(self): self.gui_log("計分伺服器連線成功", "SYS")
        def on_disconnect(self): self.gui_log("與伺服器斷開", "ERR")

    class ScoreboardServer(Scoreboard):
        def __init__(self, teamname, host, gui_log=None):
            super().__init__(gui_log)
            self.teamname, self.ip = teamname, host
            self.socket = socketio.Client()
            self.socket.register_namespace(TeamNamespace("/team", self.log_msg))
            self.socket.connect(self.ip, socketio_path="scoreboard.io")
            self.socket.emit("start_game", {"teamname": teamname}, namespace="/team")
        def add_UID(self, UID_str: str):
            res = self.socket.call("add_UID", UID_str, namespace="/team")
            return (res.get("score", 0), res.get("time_remaining", 0)) if res else (0,0)
        def get_current_score(self):
            try:
                res = requests.get(f"{self.ip}/current_score", params={"sid": self.socket.get_sid(namespace="/team")})
                return res.json()["current_score"]
            except: return None

# ==========================================
# 地圖演算法類別 (DFS MazeSolver)
# ==========================================
class MazeSolver:
    def __init__(self):
        self.rows = []
        self.adj = {}
        self.id_to_coord = {}
        self.prize_val, self.prize_bit = {}, {}
        self.num_prizes = 0
        self.memo, self.best_next = {}, {}

    def load_csv(self, path):
        self.rows = []
        with open(path, newline="", encoding="utf-8-sig") as f:
            reader = csv.DictReader(f)
            for row in reader:
                if row.get("index"): self.rows.append(row)
        return len(self.rows)

    def build_graph(self, start_node, prize_nodes):
        self.adj, self.id_to_coord, self.prize_val, self.prize_bit = {}, {}, {}, {}
        self.memo, self.best_next, self.num_prizes = {}, {}, 0
        node_ids = [int(r["index"]) for r in self.rows]
        for u in node_ids: self.adj[u] = []
        
        for row in self.rows:
            u = int(row["index"])
            for d in ["North", "South", "West", "East"]:
                if row[d].strip(): self.adj[u].append(int(float(row[d])))
        
        row_map = {int(r["index"]): r for r in self.rows}
        self.id_to_coord[start_node] = (0, 0)
        q = deque([start_node])
        mapping = {"North": (-1, 0), "South": (1, 0), "West": (0, -1), "East": (0, 1)}
        
        while q:
            u = q.popleft(); r, c = self.id_to_coord[u]
            for d, (dr, dc) in mapping.items():
                val = row_map[u][d].strip()
                if val:
                    v = int(float(val))
                    if v not in self.id_to_coord:
                        self.id_to_coord[v] = (r+dr, c+dc); q.append(v)
                        
        for n in prize_nodes:
            if n in self.id_to_coord:
                r, c = self.id_to_coord[n]; sr, sc = self.id_to_coord[start_node]
                self.prize_val[n] = (abs(r-sr) + abs(c-sc)) * 10
                self.prize_bit[n] = self.num_prizes; self.num_prizes += 1
        self.all_mask = (1 << self.num_prizes) - 1

    def dfs(self, u, k, state):
        if k == 0 or state == self.all_mask: return 0
        key = (u, k, state)
        if key in self.memo: return self.memo[key]
        
        max_f, best_v = 0, -1
        for v in self.adj[u]:
            ns, sc = state, 0
            bit = self.prize_bit.get(v, -1)
            if bit != -1 and not (state & (1 << bit)):
                ns |= (1 << bit); sc = self.prize_val[v]
            res = sc + self.dfs(v, k-1, ns)
            if res >= max_f: 
                max_f, best_v = res, v
        
        self.best_next[key], self.memo[key] = best_v, max_f
        return max_f

    def calculate(self, start, init_dir, steps, prizes):
        self.build_graph(start, prizes)
        score = self.dfs(start, steps, 0)
        
        path, curr, k, state = [start], start, steps, 0
        while k > 0:
            nxt = self.best_next.get((curr, k, state), -1)
            if nxt == -1: break
            path.append(nxt)
            bit = self.prize_bit.get(nxt, -1)
            if bit != -1: state |= (1 << bit)
            curr, k = nxt, k - 1
            
        cmds, cdir = "", init_dir
        for i in range(len(path)-1):
            r1, c1 = self.id_to_coord[path[i]]; r2, c2 = self.id_to_coord[path[i+1]]
            tdir = 0 if r2 < r1 else 2 if r2 > r1 else 1 if c2 > c1 else 3
            turn = (tdir - cdir + 4) % 4
            cmds += "F" if turn == 0 else "R" if turn == 1 else "U" if turn == 2 else "L"
            cdir = tdir
        return score, path, cmds

# ==========================================
# 主介面程式 (Win11 風格 + 雙模全功能)
# ==========================================
class CarControllerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("🚗 循跡車控制系統 (Win11 雙模全功能版)")
        self.root.geometry("1050x850")
        self.root.configure(bg="#202020")
        
        # 核心變數
        self.mode = tk.StringVar(value="BLE")
        self.is_connected = False
        self.ser = None
        self.ble_client = None
        self.ble_loop = asyncio.new_event_loop()
        self.solver = MazeSolver()
        self.scoreboard = None
        self.rfid_records = []
        
        # 參數設定檔
        self.config_file = "car_config.json"
        self.config = {
            "PORT": "COM9", "P": "24.0", "I": "0.0", "D": "140.0",
            "X": "325", "Y": "425", "Z": "605"
        }
        self.load_config()

        self.setup_ui()
        threading.Thread(target=self._run_ble_loop, daemon=True).start()

    def _run_ble_loop(self):
        asyncio.set_event_loop(self.ble_loop)
        self.ble_loop.run_forever()

    def load_config(self):
        if os.path.exists(self.config_file):
            try:
                with open(self.config_file, "r", encoding="utf-8") as f:
                    self.config.update(json.load(f))
            except: pass

    def save_config(self):
        try:
            with open(self.config_file, "w", encoding="utf-8") as f:
                json.dump(self.config, f, indent=4)
        except Exception as e:
            self.log(f"儲存設定檔失敗: {e}", "ERR")

    def apply_styles(self):
        style = ttk.Style()
        style.theme_use('clam')
        bg_main, bg_card, accent, fg_white = "#202020", "#2d2d2d", "#4cc2ff", "#ffffff"
        
        style.configure(".", background=bg_main, foreground=fg_white, font=("Microsoft JhengHei", 10))
        style.configure("TLabelframe", background=bg_card, bordercolor="#333333", borderwidth=1)
        style.configure("TLabelframe.Label", background=bg_card, foreground=accent, font=("Microsoft JhengHei", 11, "bold"))
        style.configure("TButton", background="#3f3f3f", foreground=fg_white, borderwidth=0, padding=6)
        style.map("TButton", background=[("active", accent)], foreground=[("active", "black")])
        style.configure("Accent.TButton", background=accent, foreground="black", font=("Microsoft JhengHei", 10, "bold"))
        style.configure("TNotebook", background=bg_main, borderwidth=0)
        style.configure("TNotebook.Tab", background="#1e1e1e", foreground="#888", padding=[15, 8], font=("Microsoft JhengHei", 10))
        style.map("TNotebook.Tab", background=[("selected", bg_card)], foreground=[("selected", accent)])

    def setup_ui(self):
        self.apply_styles()
        
        # --- 頂部狀態列 ---
        top = tk.Frame(self.root, bg="#202020", pady=15, padx=25)
        top.pack(fill=tk.X)
        tk.Label(top, text="🚗 循跡車控制中心", font=("Segoe UI Variable", 18, "bold"), bg="#202020", fg="white").pack(side=tk.LEFT)
        
        mode_box = tk.Frame(top, bg="#202020")
        mode_box.pack(side=tk.LEFT, padx=30)
        ttk.Radiobutton(mode_box, text="BLE 原生藍牙", variable=self.mode, value="BLE").pack(side=tk.LEFT, padx=10)
        ttk.Radiobutton(mode_box, text="COM 序列埠", variable=self.mode, value="SERIAL").pack(side=tk.LEFT, padx=10)
        
        self.btn_conn = ttk.Button(top, text="開始連線", command=self.toggle_connection, style="Accent.TButton")
        self.btn_conn.pack(side=tk.RIGHT, padx=10)
        
        self.port_var = tk.StringVar(value=self.config["PORT"])
        self.port_in = tk.Entry(top, textvariable=self.port_var, width=8, bg="#1e1e1e", fg="white", font=("Consolas", 12), insertbackground="white")
        self.port_in.pack(side=tk.RIGHT, padx=5)
        tk.Label(top, text="COM埠:", bg="#202020", fg="white").pack(side=tk.RIGHT)
        
        self.conn_status = tk.Label(top, text="未連線 🔴", bg="#202020", fg="#ff5555", font=("Microsoft JhengHei", 12, "bold"))
        self.conn_status.pack(side=tk.RIGHT, padx=20)

        # --- 分頁標籤 ---
        self.nb = ttk.Notebook(self.root)
        self.nb.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        self.tab_ctrl = tk.Frame(self.nb, bg="#2d2d2d", padx=20, pady=20)
        self.tab_map = tk.Frame(self.nb, bg="#2d2d2d", padx=20, pady=20)
        self.tab_sb = tk.Frame(self.nb, bg="#2d2d2d", padx=20, pady=20)
        self.tab_params = tk.Frame(self.nb, bg="#2d2d2d", padx=20, pady=20)
        self.tab_logs = tk.Frame(self.nb, bg="#2d2d2d", padx=20, pady=20)

        self.nb.add(self.tab_ctrl, text="🎮 控制面板")
        self.nb.add(self.tab_map, text="🗺️ 路徑規劃")
        self.nb.add(self.tab_sb, text="🏆 計分板設定")
        self.nb.add(self.tab_params, text="⚙️ 參數調整")
        self.nb.add(self.tab_logs, text="📜 系統日誌")

        self.init_tabs()

    def get_entry_style(self):
        return {"bg": "#1e1e1e", "fg": "white", "insertbackground": "white", "highlightthickness": 1, 
                "highlightbackground": "#444", "highlightcolor": "#4cc2ff", "relief": "flat"}

    def init_tabs(self):
        # ==========================================
        # 1. 🎮 控制面板
        # ==========================================
        l_ctrl = tk.LabelFrame(self.tab_ctrl, text="動作遙控", bg="#2d2d2d", fg="#4cc2ff", pady=15)
        l_ctrl.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=10)
        
        btn_f = tk.Frame(l_ctrl, bg="#2d2d2d")
        btn_f.pack(pady=20)
        b_sty = {"font": ("Segoe UI", 16, "bold"), "width": 5, "height": 2, "bg": "#3f3f3f", "fg": "white", "activebackground": "#4cc2ff", "relief": "flat"}
        tk.Button(btn_f, text="F\n↑", command=lambda: self.send_cmd("F"), **b_sty).grid(row=0, column=1, padx=8, pady=8)
        tk.Button(btn_f, text="L\n←", command=lambda: self.send_cmd("L"), **b_sty).grid(row=1, column=0, padx=8, pady=8)
        tk.Button(btn_f, text="U\n↺", command=lambda: self.send_cmd("U"), **b_sty).grid(row=1, column=1, padx=8, pady=8)
        tk.Button(btn_f, text="R\n→", command=lambda: self.send_cmd("R"), **b_sty).grid(row=1, column=2, padx=8, pady=8)
        
        tk.Label(l_ctrl, text="連續指令序列:", bg="#2d2d2d", fg="#aaa").pack(pady=(20, 5))
        self.seq_in = tk.Entry(l_ctrl, font=("Consolas", 14), **self.get_entry_style())
        self.seq_in.pack(fill=tk.X, padx=30, pady=10, ipady=4)
        ttk.Button(l_ctrl, text="發送指令", command=self.send_seq, style="Accent.TButton").pack()

        r_ctrl = tk.LabelFrame(self.tab_ctrl, text="RFID 與計分資訊", bg="#2d2d2d", fg="#4cc2ff", padx=15, pady=15)
        r_ctrl.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=10)
        
        self.score_lbl = tk.Label(r_ctrl, text="官方總分: 0", font=("Microsoft JhengHei", 24, "bold"), bg="#2d2d2d", fg="#a6e22e")
        self.score_lbl.pack(pady=10)
        
        self.rfid_list = tk.Listbox(r_ctrl, bg="#1e1e1e", fg="#ddd", font=("Consolas", 11), borderwidth=0, highlightthickness=1, highlightbackground="#444")
        self.rfid_list.pack(fill=tk.BOTH, expand=True, pady=10)
        
        # --- 新增：手動輸入 UID 區塊 ---
        manual_f = tk.Frame(r_ctrl, bg="#2d2d2d")
        manual_f.pack(fill=tk.X, pady=(0, 10))
        self.manual_uid_in = tk.Entry(manual_f, font=("Consolas", 12), **self.get_entry_style())
        self.manual_uid_in.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))
        self.manual_uid_in.bind("<Return>", lambda e: self.manual_add_uid()) # 支援按 Enter 送出
        ttk.Button(manual_f, text="手動送出", command=self.manual_add_uid).pack(side=tk.RIGHT)
        # -----------------------------

        ttk.Button(r_ctrl, text="清空本地紀錄", command=lambda: (self.rfid_list.delete(0, tk.END), self.rfid_records.clear())).pack()

        # ==========================================
        # 2. 🗺️ 路徑規劃
        # ==========================================
        f_map = tk.Frame(self.tab_map, bg="#2d2d2d")
        f_map.pack(fill=tk.X, pady=10)
        ttk.Button(f_map, text="📁 載入 maze.csv", command=self.load_maze_csv).pack(side=tk.LEFT)
        self.maze_status = tk.Label(f_map, text="尚未載入地圖", bg="#2d2d2d", fg="#888", padx=15)
        self.maze_status.pack(side=tk.LEFT)
        
        cfg_map = tk.LabelFrame(self.tab_map, text="演算法設定", bg="#2d2d2d", fg="#4cc2ff", padx=15, pady=15)
        cfg_map.pack(fill=tk.X, pady=10)
        
        self.start_node = tk.Entry(cfg_map, width=6, font=("Arial", 11), **self.get_entry_style()); self.start_node.insert(0, "1")
        tk.Label(cfg_map, text="起點 Node:", bg="#2d2d2d", fg="white").pack(side=tk.LEFT, padx=5)
        self.start_node.pack(side=tk.LEFT)
        
        self.map_dir = tk.StringVar(value="3")
        tk.Label(cfg_map, text="初始方向:", bg="#2d2d2d", fg="white").pack(side=tk.LEFT, padx=(15, 5))
        ttk.Combobox(cfg_map, textvariable=self.map_dir, values=["0", "1", "2", "3"], width=5, state="readonly").pack(side=tk.LEFT)
        tk.Label(cfg_map, text="(0北 1東 2南 3西)", bg="#2d2d2d", fg="#888").pack(side=tk.LEFT, padx=5)

        self.prizes = tk.Entry(cfg_map, width=40, font=("Arial", 11), **self.get_entry_style()); self.prizes.insert(0, "1,6,12,13,16,22,34,43,46,47")
        tk.Label(cfg_map, text="獎品點:", bg="#2d2d2d", fg="white").pack(side=tk.LEFT, padx=(15, 5))
        self.prizes.pack(side=tk.LEFT)

        ttk.Button(self.tab_map, text="🚀 計算最佳路徑並同步", command=self.run_dfs_solver, style="Accent.TButton").pack(pady=15, ipady=4)
        self.res_txt = scrolledtext.ScrolledText(self.tab_map, height=8, bg="#1e1e1e", fg="#4cc2ff", font=("Consolas", 11), bd=0)
        self.res_txt.pack(fill=tk.BOTH, expand=True)

        # ==========================================
        # 3. 🏆 計分板
        # ==========================================
        sb_f = tk.LabelFrame(self.tab_sb, text="計分板連線設定", bg="#2d2d2d", fg="#4cc2ff", padx=20, pady=20)
        sb_f.pack(fill=tk.X)
        self.sb_mode = tk.StringVar(value="1")
        ttk.Radiobutton(sb_f, text="Server 伺服器", variable=self.sb_mode, value="0").pack(anchor=tk.W, pady=5)
        ttk.Radiobutton(sb_f, text="Fake 本地測試", variable=self.sb_mode, value="1").pack(anchor=tk.W, pady=5)
        
        self.sb_team = tk.Entry(sb_f, width=30, **self.get_entry_style()); self.sb_team.insert(0, "YOUR_TEAM")
        tk.Label(sb_f, text="隊伍名稱:", bg="#2d2d2d", fg="#aaa").pack(anchor=tk.W, pady=(15, 2))
        self.sb_team.pack(anchor=tk.W)

        self.sb_url_in = tk.Entry(sb_f, width=50, **self.get_entry_style()); self.sb_url_in.insert(0, "http://carcar.ntuee.org/scoreboard")
        tk.Label(sb_f, text="伺服器 URL:", bg="#2d2d2d", fg="#aaa").pack(anchor=tk.W, pady=(15, 2))
        self.sb_url_in.pack(anchor=tk.W)
        
        ttk.Button(self.tab_sb, text="🚀 初始化計分板", command=self.init_sb_system, style="Accent.TButton").pack(pady=30, ipady=4)

        # ==========================================
        # 4. ⚙️ 參數調整
        # ==========================================
        p_top = tk.Frame(self.tab_params, bg="#2d2d2d")
        p_top.pack(fill=tk.X, pady=(0, 15))
        
        pid_f = tk.LabelFrame(p_top, text="PID 設定", bg="#2d2d2d", fg="#4cc2ff", padx=15, pady=15)
        pid_f.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 10))
        turn_f = tk.LabelFrame(p_top, text="轉彎延遲 (ms)", bg="#2d2d2d", fg="#4cc2ff", padx=15, pady=15)
        turn_f.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        self.p_var = tk.StringVar(value=self.config["P"])
        self.i_var = tk.StringVar(value=self.config["I"])
        self.d_var = tk.StringVar(value=self.config["D"])
        self.x_var = tk.StringVar(value=self.config["X"])
        self.y_var = tk.StringVar(value=self.config["Y"])
        self.z_var = tk.StringVar(value=self.config["Z"])

        def make_param_row(parent, label, var, p_key, is_int=False):
            f = tk.Frame(parent, bg="#2d2d2d")
            f.pack(fill=tk.X, pady=5)
            tk.Label(f, text=label, width=6, bg="#2d2d2d", fg="white", font=("Consolas", 11, "bold")).pack(side=tk.LEFT)
            tk.Entry(f, textvariable=var, width=10, font=("Arial", 11), **self.get_entry_style()).pack(side=tk.LEFT, padx=10)
            ttk.Button(f, text="套用", command=lambda: self.send_param(p_key, var.get(), int if is_int else float)).pack(side=tk.RIGHT)

        make_param_row(pid_f, "Kp:", self.p_var, "P")
        make_param_row(pid_f, "Ki:", self.i_var, "I")
        make_param_row(pid_f, "Kd:", self.d_var, "D")
        make_param_row(turn_f, "左(X):", self.x_var, "X", True)
        make_param_row(turn_f, "右(Y):", self.y_var, "Y", True)
        make_param_row(turn_f, "迴(Z):", self.z_var, "Z", True)

        tk.Label(self.tab_params, text="參數修改紀錄:", bg="#2d2d2d", fg="#aaa").pack(anchor=tk.W)
        self.param_hist = scrolledtext.ScrolledText(self.tab_params, bg="#1e1e1e", fg="#ddd", font=("Consolas", 10), bd=0)
        self.param_hist.pack(fill=tk.BOTH, expand=True, pady=5)

        # ==========================================
        # 5. 📜 系統日誌
        # ==========================================
        btn_f = tk.Frame(self.tab_logs, bg="#2d2d2d")
        btn_f.pack(fill=tk.X, pady=(0, 10))
        ttk.Button(btn_f, text="清除日誌", command=lambda: self.sys_logs.delete(1.0, tk.END)).pack(side=tk.RIGHT)
        self.sys_logs = scrolledtext.ScrolledText(self.tab_logs, bg="#141414", fg="#a6e22e", font=("Consolas", 10), bd=0)
        self.sys_logs.pack(fill=tk.BOTH, expand=True)

    def log(self, msg, t="SYS"):
        now = time.strftime("%H:%M:%S")
        prefix = f"[{now}] ⚙️ SYS:"
        if t == "TX": prefix = f"[{now}] 📤 TX:"
        elif t == "RX": prefix = f"[{now}] 📥 RX:"
        elif t == "ERR": prefix = f"[{now}] ❌ ERR:"
        self.sys_logs.insert(tk.END, f"{prefix} {msg}\n")
        self.sys_logs.see(tk.END)

    def toggle_connection(self):
        if self.is_connected: self.disconnect_all()
        else:
            self.config["PORT"] = self.port_var.get().strip()
            self.save_config()
            if self.mode.get() == "SERIAL": self.connect_serial()
            else: self.connect_ble()

    def connect_serial(self):
        p = self.port_var.get().strip()
        try:
            self.ser = serial.Serial(p, 9600, timeout=0.1)
            self.is_connected = True; self.update_ui_state(True)
            self.log(f"Serial 連線成功: {p}")
            threading.Thread(target=self._serial_listener, daemon=True).start()
        except Exception as e: messagebox.showerror("錯誤", f"無法開啟 {p}\n請確認車子已開機且 COM 埠正確。\n錯誤訊息: {e}")

    def _serial_listener(self):
        while self.is_connected and self.ser:
            try:
                if self.ser.in_waiting:
                    l = self.ser.readline().decode(errors='ignore').strip()
                    if l: self.root.after(0, lambda msg=l: self.process_msg(msg))
            except: break
            time.sleep(0.05)

    def connect_ble(self):
        if not HAS_BLE or BleakScanner is None:
            messagebox.showerror("錯誤", "請先安裝 bleak: pip install bleak"); return
        self.btn_conn.config(state='disabled'); self.log("掃描原生藍牙裝置中...")
        asyncio.run_coroutine_threadsafe(self._ble_connect_task(), self.ble_loop)

    async def _ble_connect_task(self):
        try:
            devs = await BleakScanner.discover(timeout=4.0)
            target = next((d for d in devs if d.name and ("HM6" in d.name or "HMSoft" in d.name or "BT05" in d.name)), None)
            if not target: 
                self.log("找不到藍牙裝置，請確認車子電源。", "ERR")
                self.root.after(0, lambda: self.btn_conn.config(state='normal'))
                return
            
            self.ble_client = BleakClient(target.address)
            await self.ble_client.connect()
            self.is_connected = True
            self.root.after(0, lambda: self.update_ui_state(True))
            self.log(f"BLE 連線成功: {target.name}")
            await self.ble_client.start_notify(UART_CHAR_UUID, lambda s, d: self.process_msg(d.decode(errors='ignore').strip()))
        except Exception as e: 
            self.log(f"BLE 失敗: {e}", "ERR")
            self.root.after(0, lambda: self.update_ui_state(False))

    def send_cmd(self, data):
        if not self.is_connected:
            messagebox.showwarning("未連線", "請先連線藍牙！"); return
        try:
            msg = (data + "\n").encode()
            if self.mode.get() == "SERIAL" and self.ser: self.ser.write(msg)
            else: asyncio.run_coroutine_threadsafe(self.ble_client.write_gatt_char(UART_CHAR_UUID, msg), self.ble_loop)
            self.log(data, "TX")
        except Exception as e: self.log(f"發送失敗: {e}", "ERR")

    def send_seq(self):
        s = self.seq_in.get().strip().upper()
        invalid = [c for c in s if c not in set("LRUF")]
        if invalid:
            messagebox.showerror("錯誤", "序列僅限 L, R, U, F")
            return
        if s: threading.Thread(target=self._send_long_seq, args=(s,), daemon=True).start()

    def _send_long_seq(self, seq):
        self.log(f"開始發送長序列: {seq}", "TX")
        for i in range(0, len(seq), 15):
            chunk = seq[i:i+15]
            self.send_cmd(chunk)
            time.sleep(0.1)
        self.root.after(0, lambda: self.seq_in.delete(0, tk.END))

    def send_param(self, param, value, v_type):
        try:
            val = v_type(value)
            self.send_cmd(f"{param}{val}")
            self.param_hist.insert(tk.END, f"[{time.strftime('%H:%M:%S')}] 設定 {param} = {val}\n")
            self.param_hist.see(tk.END)
            self.config[param] = str(val)
            self.save_config()
        except ValueError: messagebox.showerror("錯誤", "數值格式不正確")

    # --- 新增：手動加入 UID 的邏輯 ---
    def manual_add_uid(self):
        uid = self.manual_uid_in.get().strip().upper() # 自動轉大寫與去空白
        if not uid: return
        
        self.log(f"手動輸入 UID: {uid}", "SYS")
        self.rfid_list.insert(tk.END, f" #{len(self.rfid_records)+1:02d} | UID: {uid} (手動)")
        self.rfid_list.yview(tk.END)
        self.rfid_records.append(uid)
        
        if self.scoreboard: 
            threading.Thread(target=self._report_score, args=(uid,), daemon=True).start()
        else:
            self.log("⚠️ 尚未初始化計分板！請先至「計分板設定」點擊初始化", "ERR")
            
        self.manual_uid_in.delete(0, tk.END)
    # ---------------------------------

    def process_msg(self, msg):
        self.log(msg, "RX")
        if msg.startswith("UID:"):
            uid = msg.split(":")[1].strip().upper()
            self.rfid_list.insert(tk.END, f" #{len(self.rfid_records)+1:02d} | UID: {uid}")
            self.rfid_list.yview(tk.END)
            self.rfid_records.append(uid)
            if self.scoreboard: 
                threading.Thread(target=self._report_score, args=(uid,), daemon=True).start()
            else:
                self.log("⚠️ 尚未初始化計分板！請先至「計分板設定」點擊初始化", "ERR")

    def _report_score(self, uid):
        try:
            s, t = self.scoreboard.add_UID(uid)
            score = self.scoreboard.get_current_score()
            if score is not None:
                self.root.after(0, lambda: self.score_lbl.config(text=f"官方總分: {score}"))
        except Exception as e: self.log(f"報分錯誤: {e}", "ERR")

    def init_sb_system(self):
        try:
            team = self.sb_team.get().strip()
            if self.sb_mode.get() == "0":
                if not HAS_SOCKETIO: messagebox.showerror("錯誤", "未安裝 python-socketio 套件"); return
                self.scoreboard = ScoreboardServer(team, self.sb_url_in.get().strip(), self.log)
            else:
                p = filedialog.askopenfilename(title="選擇 fakeUID.csv", filetypes=[("CSV", "*.csv")])
                if p: self.scoreboard = ScoreboardFake(team, p, self.log)
            messagebox.showinfo("成功", "計分板系統初始化成功！")
            self.score_lbl.config(text="官方總分: 0")
        except Exception as e: messagebox.showerror("失敗", f"初始化失敗: {e}")

    def load_maze_csv(self):
        p = filedialog.askopenfilename(filetypes=[("CSV Files", "*.csv")])
        if p:
            n = self.solver.load_csv(p)
            self.maze_status.config(text=f"✅ 已載入 ({n} nodes)", fg="#a6e22e")
            self.log(f"載入地圖: {os.path.basename(p)}")

    def run_dfs_solver(self):
        if not self.solver.rows: messagebox.showwarning("警告", "請先載入地圖 CSV！"); return
        try:
            sn = int(self.start_node.get())
            dr = int(self.map_dir.get())
            pn = [int(x.strip()) for x in self.prizes.get().split(',') if x.strip().isdigit()]
            
            sc, path, cmds = self.solver.calculate(sn, dr, 80, pn)
            
            self.res_txt.delete(1.0, tk.END)
            self.res_txt.insert(tk.END, f"最高預測分數: {sc}\n")
            self.res_txt.insert(tk.END, f"路徑: {' ➔ '.join(map(str, path))}\n")
            self.res_txt.insert(tk.END, f"產出指令: {cmds}")
            
            self.seq_in.delete(0, tk.END); self.seq_in.insert(0, cmds)
            self.nb.select(self.tab_ctrl)
            self.log("DFS 路徑計算完成，指令已同步至控制面板", "SYS")
        except Exception as e: messagebox.showerror("計算失敗", f"參數錯誤或演算法例外: {e}")

    def disconnect_all(self):
        self.is_connected = False
        if self.ser: self.ser.close(); self.ser = None
        if self.ble_client: asyncio.run_coroutine_threadsafe(self.ble_client.disconnect(), self.ble_loop)
        self.update_ui_state(False); self.log("連線已中斷。")

    def update_ui_state(self, conn):
        s, c = ("已連線 🟢", "#a6e22e") if conn else ("未連線 🔴", "#ff5555")
        self.conn_status.config(text=s, fg=c)
        self.btn_conn.config(text="斷開連線" if conn else "開始連線", state='normal')

if __name__ == "__main__":
    root = tk.Tk()
    app = CarControllerApp(root)
    root.mainloop()