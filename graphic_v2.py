import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
import json
import time
import math
from dataclasses import dataclass
from typing import List, Tuple, Optional

# Cài đặt một lần: pip install tkintermapview
from tkintermapview import TkinterMapView

# ------------------- Hàm tính khoảng cách Haversine -------------------
def distance_km(lat1, lon1, lat2, lon2):
    R = 6371.0
    lat1_rad = math.radians(lat1)
    lon1_rad = math.radians(lon1)
    lat2_rad = math.radians(lat2)
    lon2_rad = math.radians(lon2)

    dlat = lat2_rad - lat1_rad
    dlon = lon2_rad - lon1_rad

    a = math.sin(dlat / 2)**2 + math.cos(lat1_rad) * math.cos(lat2_rad) * math.sin(dlon / 2)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))

    return R * c

# ------------------- Các class cho R-Tree (giữ nguyên) -------------------
@dataclass
class Point:
    lat: float
    lon: float
    data: dict
    
    def distance_to(self, other: 'Point') -> float:
        R = 6371
        lat1, lon1 = math.radians(self.lat), math.radians(self.lon)
        lat2, lon2 = math.radians(other.lat), math.radians(other.lon)
        
        dlat = lat2 - lat1
        dlon = lon2 - lon1
        
        a = math.sin(dlat/2)**2 + math.cos(lat1) * math.cos(lat2) * math.sin(dlon/2)**2
        c = 2 * math.asin(math.sqrt(a))
        return R * c

@dataclass
class MBR:
    min_lat: float
    max_lat: float
    min_lon: float
    max_lon: float
    
    def area(self) -> float:
        return (self.max_lat - self.min_lat) * (self.max_lon - self.min_lon)
    
    def intersects_square(self, center_lat: float, center_lon: float, 
                          half_side_lat: float, half_side_lon: float) -> bool:
        square_min_lat = center_lat - half_side_lat
        square_max_lat = center_lat + half_side_lat
        square_min_lon = center_lon - half_side_lon
        square_max_lon = center_lon + half_side_lon
        
        if self.max_lat < square_min_lat: return False
        if self.min_lat > square_max_lat: return False
        if self.max_lon < square_min_lon: return False
        if self.min_lon > square_max_lon: return False
        return True
    
    def expand_to_include(self, point: Point) -> 'MBR':
        return MBR(
            min(self.min_lat, point.lat),
            max(self.max_lat, point.lat),
            min(self.min_lon, point.lon),
            max(self.max_lon, point.lon)
        )
    
    def expand_to_include_mbr(self, other: 'MBR') -> 'MBR':
        return MBR(
            min(self.min_lat, other.min_lat),
            max(self.max_lat, other.max_lat),
            min(self.min_lon, other.min_lon),
            max(self.max_lon, other.max_lon)
        )
    
    @staticmethod
    def from_point(point: Point) -> 'MBR':
        return MBR(point.lat, point.lat, point.lon, point.lon)

class RTreeNode:
    def __init__(self, is_leaf: bool = True, parent=None):
        self.is_leaf = is_leaf
        self.mbr: Optional[MBR] = None
        self.entries: List[Tuple[MBR, any]] = []
        self.parent = parent
    
    def is_full(self, max_entries: int) -> bool:
        return len(self.entries) >= max_entries
    
    def update_mbr(self):
        if not self.entries:
            self.mbr = None
            return
        mbr = self.entries[0][0]
        for entry_mbr, _ in self.entries[1:]:
            mbr = mbr.expand_to_include_mbr(entry_mbr)
        self.mbr = mbr

class RTree:
    def __init__(self, max_entries: int = 5):
        self.max_entries = max_entries
        self.min_entries = max(2, max_entries // 2)
        self.root = RTreeNode(is_leaf=True)
    
    def insert(self, point: Point):
        mbr = MBR.from_point(point)
        leaf = self._choose_leaf(self.root, mbr)
        leaf.entries.append((mbr, point))
        leaf.update_mbr()
        if len(leaf.entries) > self.max_entries:
            self._handle_overflow(leaf)
    
    def _choose_leaf(self, node: RTreeNode, mbr: MBR) -> RTreeNode:
        if node.is_leaf:
            return node
        best_entry = None
        min_enlargement = float('inf')
        min_area = float('inf')
        for entry_mbr, child_node in node.entries:
            enlarged_mbr = entry_mbr.expand_to_include_mbr(mbr)
            enlargement = enlarged_mbr.area() - entry_mbr.area()
            if enlargement < min_enlargement or (enlargement == min_enlargement and entry_mbr.area() < min_area):
                min_enlargement = enlargement
                min_area = entry_mbr.area()
                best_entry = child_node
        return self._choose_leaf(best_entry, mbr)
    
    def _handle_overflow(self, node: RTreeNode):
        node1, node2 = self._split_node(node)
        if node.parent is None:
            new_root = RTreeNode(is_leaf=False)
            new_root.entries.append((node1.mbr, node1))
            new_root.entries.append((node2.mbr, node2))
            new_root.update_mbr()
            node1.parent = new_root
            node2.parent = new_root
            self.root = new_root
        else:
            parent = node.parent
            new_entries = [e for e in parent.entries if e[1] is not node]
            parent.entries = new_entries
            parent.entries.append((node1.mbr, node1))
            parent.entries.append((node2.mbr, node2))
            parent.update_mbr()
            if len(parent.entries) > self.max_entries:
                self._handle_overflow(parent)
    
    def _split_node(self, node: RTreeNode) -> Tuple[RTreeNode, RTreeNode]:
        seed1_idx, seed2_idx = self._linear_pick_seeds(node.entries)
        node1 = RTreeNode(is_leaf=node.is_leaf, parent=node.parent)
        node2 = RTreeNode(is_leaf=node.is_leaf, parent=node.parent)
        node1.entries.append(node.entries[seed1_idx])
        node2.entries.append(node.entries[seed2_idx])
        if not node.is_leaf:
            node.entries[seed1_idx][1].parent = node1
            node.entries[seed2_idx][1].parent = node2
        remaining = [e for i, e in enumerate(node.entries) if i != seed1_idx and i != seed2_idx]
        for entry in remaining:
            mbr, data = entry
            node1.update_mbr()
            node2.update_mbr()
            enlarged1 = node1.mbr.expand_to_include_mbr(mbr)
            enlarged2 = node2.mbr.expand_to_include_mbr(mbr)
            enlargement1 = enlarged1.area() - node1.mbr.area()
            enlargement2 = enlarged2.area() - node2.mbr.area()
            if enlargement1 < enlargement2:
                target_node = node1
            elif enlargement2 < enlargement1:
                target_node = node2
            else:
                if node1.mbr.area() < node2.mbr.area():
                    target_node = node1
                elif node2.mbr.area() < node1.mbr.area():
                    target_node = node2
                else:
                    target_node = node1 if len(node1.entries) <= len(node2.entries) else node2
            target_node.entries.append(entry)
            if not node.is_leaf:
                data.parent = target_node
        node1.update_mbr()
        node2.update_mbr()
        return node1, node2
    
    def _linear_pick_seeds(self, entries: List[Tuple[MBR, any]]) -> Tuple[int, int]:
        max_separation = -float('inf')
        seed1_idx = 0
        seed2_idx = 1 if len(entries) > 1 else 0
        for dim in ['lat', 'lon']:
            if dim == 'lat':
                min_of_max = min(mbr.max_lat for mbr, _ in entries)
                max_of_min = max(mbr.min_lat for mbr, _ in entries)
                overall_min = min(mbr.min_lat for mbr, _ in entries)
                overall_max = max(mbr.max_lat for mbr, _ in entries)
                width = overall_max - overall_min
                if width > 0:
                    separation = (max_of_min - min_of_max) / width
                    if separation > max_separation:
                        max_separation = separation
                        for i, (mbr, _) in enumerate(entries):
                            if mbr.min_lat == max_of_min: seed1_idx = i
                            if mbr.max_lat == min_of_max: seed2_idx = i
            else:
                min_of_max = min(mbr.max_lon for mbr, _ in entries)
                max_of_min = max(mbr.min_lon for mbr, _ in entries)
                overall_min = min(mbr.min_lon for mbr, _ in entries)
                overall_max = max(mbr.max_lon for mbr, _ in entries)
                width = overall_max - overall_min
                if width > 0:
                    separation = (max_of_min - min_of_max) / width
                    if separation > max_separation:
                        max_separation = separation
                        for i, (mbr, _) in enumerate(entries):
                            if mbr.min_lon == max_of_min: seed1_idx = i
                            if mbr.max_lon == min_of_max: seed2_idx = i
        if seed1_idx == seed2_idx and len(entries) > 1:
            seed2_idx = (seed1_idx + 1) % len(entries)
        return seed1_idx, seed2_idx
    
    def search_square(self, center: Point, radius_km: float) -> List[Tuple[Point, float]]:
        half_side_lat = radius_km / 111.0
        half_side_lon = radius_km / (111.0 * math.cos(math.radians(center.lat)))
        candidates = []
        self._search_square_recursive(self.root, center.lat, center.lon,
                                      half_side_lat, half_side_lon, center, candidates)
        results = [(point, dist) for point, dist in candidates if dist <= radius_km]
        results.sort(key=lambda x: x[1])
        return results
    
    def _search_square_recursive(self, node: RTreeNode, center_lat: float, center_lon: float,
                                 half_side_lat: float, half_side_lon: float,
                                 center_point: Point, results: List[Tuple[Point, float]]):
        if not node or not node.mbr:
            return
        if not node.mbr.intersects_square(center_lat, center_lon, half_side_lat, half_side_lon):
            return
        if node.is_leaf:
            square_min_lat = center_lat - half_side_lat
            square_max_lat = center_lat + half_side_lat
            square_min_lon = center_lon - half_side_lon
            square_max_lon = center_lon + half_side_lon
            for mbr, point in node.entries:
                if (square_min_lat <= point.lat <= square_max_lat and
                    square_min_lon <= point.lon <= square_max_lon):
                    results.append((point, center_point.distance_to(point)))
        else:
            for mbr, child_node in node.entries:
                if child_node:
                    self._search_square_recursive(child_node, center_lat, center_lon,
                                                  half_side_lat, half_side_lon, center_point, results)

# ------------------- Giao diện chính -------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("So sánh Linear Search và R-Tree - Tìm trạm xăng gần nhất")
        self.geometry("1300x900")

        # Phần tải dữ liệu
        top_frame = ttk.Frame(self)
        top_frame.pack(fill="x", padx=10, pady=5)

        ttk.Label(top_frame, text="Đường dẫn file JSON:").grid(row=0, column=0, sticky="w")
        self.file_entry = ttk.Entry(top_frame, width=70)
        self.file_entry.grid(row=0, column=1, padx=5)

        ttk.Label(top_frame, text="Max entries per node:").grid(row=1, column=0, sticky="w")
        self.max_entries_entry = ttk.Entry(top_frame, width=10)
        self.max_entries_entry.insert(0, "5")
        self.max_entries_entry.grid(row=1, column=1, sticky="w", padx=5)

        ttk.Button(top_frame, text="Tải dữ liệu", command=self.load_data).grid(row=0, column=2, rowspan=2, padx=10)

        # Bản đồ
        map_frame = ttk.Frame(self)
        map_frame.pack(fill="both", expand=True, padx=10, pady=5)

        self.map_widget = TkinterMapView(map_frame, width=1200, height=500, corner_radius=0)
        self.map_widget.pack(fill="both", expand=True)

        self.map_widget.set_position(16.0, 108.0)  # Trung tâm Việt Nam
        self.map_widget.set_zoom(6)

        # Các marker và khu vực tìm kiếm
        self.current_marker = None      # Marker điểm tâm (đỏ)
        self.all_markers = []           # Tất cả trạm xăng (vàng)
        self.result_markers = []        # Trạm tìm được (xanh)
        self.search_area = None         # Vòng tròn hoặc hình vuông

        # Click để chọn điểm tâm
        def on_map_click(coord):
            lat, lon = coord
            self.lat_entry.delete(0, tk.END)
            self.lat_entry.insert(0, f"{lat:.6f}")
            self.lon_entry.delete(0, tk.END)
            self.lon_entry.insert(0, f"{lon:.6f}")

            if self.current_marker:
                self.current_marker.delete()
            self.current_marker = self.map_widget.set_marker(lat, lon, text="ĐIỂM TÌM KIẾM",
                                                            marker_color_circle="red",
                                                            marker_color_outside="darkred",
                                                            font=("Arial Bold", 12))

        self.map_widget.add_left_click_map_command(on_map_click)

        # Phần điều khiển
        control_frame = ttk.Frame(self)
        control_frame.pack(fill="x", padx=10, pady=5)

        ttk.Label(control_frame, text="Latitude:").grid(row=0, column=0, sticky="w", padx=5)
        self.lat_entry = ttk.Entry(control_frame, width=20)
        self.lat_entry.grid(row=0, column=1, padx=5)

        ttk.Label(control_frame, text="Longitude:").grid(row=0, column=2, sticky="w", padx=5)
        self.lon_entry = ttk.Entry(control_frame, width=20)
        self.lon_entry.grid(row=0, column=3, padx=5)

        ttk.Label(control_frame, text="Bán kính (km):").grid(row=0, column=4, sticky="w", padx=5)
        self.r_entry = ttk.Entry(control_frame, width=15)
        self.r_entry.insert(0, "10")
        self.r_entry.grid(row=0, column=5, padx=5)

        self.linear_btn = ttk.Button(control_frame, text="Tìm kiếm Linear", command=self.linear_search, state="disabled")
        self.linear_btn.grid(row=0, column=6, padx=20)

        self.rtree_btn = ttk.Button(control_frame, text="Tìm kiếm R-Tree", command=self.rtree_search, state="disabled")
        self.rtree_btn.grid(row=0, column=7, padx=20)

        # Kết quả text
        self.output_text = scrolledtext.ScrolledText(self, width=140, height=20)
        self.output_text.pack(fill="both", expand=True, padx=10, pady=10)

        self.data_list = None
        self.rtree = None
        self.current_max_entries = 5

    def clear_all_markers(self):
        for marker in self.all_markers:
            marker.delete()
        self.all_markers.clear()

    def clear_result_markers(self):
        for marker in self.result_markers:
            marker.delete()
        self.result_markers.clear()
        if self.search_area:
            self.search_area.delete()
            self.search_area = None

    def add_all_markers(self):
        """Hiển thị tất cả trạm xăng (màu vàng)"""
        self.clear_all_markers()
        for item in self.data_list:
            lat = item['coordinates'][0]
            lon = item['coordinates'][1]
            name = item.get('name', 'Trạm xăng')
            brand = item.get('brand', '')
            text = f"{name}" if not brand else f"{name} ({brand})"
            marker = self.map_widget.set_marker(lat, lon, text=text,
                                               marker_color_circle="yellow",
                                               marker_color_outside="orange",
                                               font=("Arial", 8))
            self.all_markers.append(marker)

        # Zoom toàn bộ dữ liệu
        if self.data_list:
            lats = [item['coordinates'][0] for item in self.data_list]
            lons = [item['coordinates'][1] for item in self.data_list]
            min_lat, max_lat = min(lats), max(lats)
            min_lon, max_lon = min(lons), max(lons)
            padding = 0.1
            self.map_widget.fit_bounding_box(
                (max_lat + padding, min_lon - padding),
                (min_lat - padding, max_lon + padding)
            )

    def add_result_markers(self, results, lat, lon, r, is_rtree=False):
        """Hiển thị marker kết quả + khu vực tìm kiếm (vòng tròn cho Linear, vuông cho R-Tree)"""
        self.clear_result_markers()

        # Tính half_side cho hình vuông (dùng cho cả zoom)
        half_side_lat = r / 111.0
        half_side_lon = r / (111.0 * math.cos(math.radians(lat)))

        if is_rtree:
            # Vẽ HÌNH VUÔNG cho R-Tree
            points = [
                (lat + half_side_lat, lon - half_side_lon),  # top-left
                (lat + half_side_lat, lon + half_side_lon),  # top-right
                (lat - half_side_lat, lon + half_side_lon),  # bottom-right
                (lat - half_side_lat, lon - half_side_lon),  # bottom-left
                (lat + half_side_lat, lon - half_side_lon)   # đóng lại
            ]
            self.search_area = self.map_widget.set_path(points, color="red", width=3)  # Màu đỏ để phân biệt
        else:
            # Vẽ VÒNG TRÒN cho Linear
            points = []
            num_points = 72
            for i in range(num_points):
                angle = math.radians(i * 360 / num_points)
                dlat = half_side_lat * math.sin(angle)
                dlon = half_side_lon * math.cos(angle)
                points.append((lat + dlat, lon + dlon))
            points.append(points[0])  # đóng vòng
            self.search_area = self.map_widget.set_path(points, color="blue", width=3)

        # Marker cho các trạm tìm được
        for point, dist in results:
            name = point.data.get('name', 'Trạm xăng')
            brand = point.data.get('brand', '')
            text = f"{name} ({brand})\n{dist:.2f} km"
            marker = self.map_widget.set_marker(point.lat, point.lon, text=text,
                                               marker_color_circle="green",
                                               marker_color_outside="darkgreen",
                                               font=("Arial Bold", 10))
            self.result_markers.append(marker)

        # Zoom vừa khu vực tìm kiếm
        padding = 0.02
        max_dlat = half_side_lat + padding
        max_dlon = half_side_lon + padding
        self.map_widget.fit_bounding_box(
            (lat + max_dlat, lon - max_dlon),
            (lat - max_dlat, lon + max_dlon)
        )

    def load_data(self):
        file_path = self.file_entry.get().strip()
        if not file_path:
            messagebox.showerror("Lỗi", "Vui lòng nhập đường dẫn file JSON!")
            return

        try:
            max_entries = int(self.max_entries_entry.get().strip())
            if max_entries < 2:
                raise ValueError
            self.current_max_entries = max_entries
        except:
            messagebox.showwarning("Cảnh báo", "Max entries không hợp lệ, dùng mặc định 5")
            self.current_max_entries = 5
            self.max_entries_entry.delete(0, tk.END)
            self.max_entries_entry.insert(0, "5")

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                self.data_list = json.load(f)
            
            self.output_text.delete(1.0, tk.END)
            self.output_text.insert(tk.END, f"Đã tải {len(self.data_list)} trạm xăng.\n")
            self.output_text.insert(tk.END, f"Đang xây dựng R-Tree (max_entries = {self.current_max_entries})...\n")
            self.update_idletasks()

            self.rtree = RTree(max_entries=self.current_max_entries)
            for item in self.data_list:
                point = Point(lat=item['coordinates'][0], lon=item['coordinates'][1], data=item)
                self.rtree.insert(point)

            self.output_text.insert(tk.END, "Xây dựng R-Tree hoàn tất!\n\n")
            self.linear_btn.config(state="normal")
            self.rtree_btn.config(state="normal")

            # Hiển thị tất cả trạm xăng
            self.clear_result_markers()
            if self.current_marker:
                self.current_marker.delete()
                self.current_marker = None
            self.add_all_markers()

        except Exception as e:
            messagebox.showerror("Lỗi", str(e))

    def get_inputs(self):
        try:
            lat = float(self.lat_entry.get())
            lon = float(self.lon_entry.get())
            r = float(self.r_entry.get())
            if r <= 0:
                raise ValueError
            return lat, lon, r
        except:
            messagebox.showerror("Lỗi", "Vui lòng chọn điểm trên bản đồ và nhập bán kính hợp lệ (>0)!")
            return None

    def linear_search(self):
        inputs = self.get_inputs()
        if not inputs or not self.data_list:
            return
        lat, lon, r = inputs

        self.output_text.insert(tk.END, "\n" + "="*100 + "\n")
        self.output_text.insert(tk.END, "LINEAR SEARCH (tìm chính xác trong hình tròn)\n")
        self.output_text.insert(tk.END, f"Tâm: ({lat:.6f}, {lon:.6f}) | Bán kính: {r} km\n")

        start = time.perf_counter()
        results = []
        for station in self.data_list:
            dist = distance_km(lat, lon, station["coordinates"][0], station["coordinates"][1])
            if dist <= r:
                point = Point(lat=station["coordinates"][0], lon=station["coordinates"][1], data=station)
                results.append((point, dist))
        results.sort(key=lambda x: x[1])
        end = time.perf_counter()
        elapsed = (end - start) * 1000

        self.output_text.insert(tk.END, f"Thời gian: {elapsed:.3f} ms\n")
        self.output_text.insert(tk.END, f"Tìm thấy {len(results)} trạm:\n")
        self.output_text.insert(tk.END, "-"*100 + "\n")
        for i, (point, dist) in enumerate(results, 1):
            data = point.data
            self.output_text.insert(tk.END,
                f"{i}. {data.get('name', 'N/A')} ({data.get('brand', 'N/A')})\n"
                f"   Địa chỉ: {data.get('display_name', 'N/A')}\n"
                f"   Khoảng cách: {dist:.2f} km\n"
                f"   Tọa độ: ({point.lat:.6f}, {point.lon:.6f})\n\n")
        self.output_text.see(tk.END)

        # Vẽ vòng tròn (xanh)
        self.add_result_markers(results, lat, lon, r, is_rtree=False)

    def rtree_search(self):
        inputs = self.get_inputs()
        if not inputs or not self.rtree:
            return
        lat, lon, r = inputs

        self.output_text.insert(tk.END, "\n" + "="*100 + "\n")
        self.output_text.insert(tk.END, "R-TREE SEARCH (tìm candidate trong hình vuông, lọc lại theo bán kính)\n")
        self.output_text.insert(tk.END, f"Tâm: ({lat:.6f}, {lon:.6f}) | Bán kính: {r} km\n")
        self.output_text.insert(tk.END, f"(max_entries = {self.current_max_entries})\n")

        center = Point(lat, lon, {})
        start = time.perf_counter()
        results = self.rtree.search_square(center, r)
        end = time.perf_counter()
        elapsed = (end - start) * 1000

        self.output_text.insert(tk.END, f"Thời gian: {elapsed:.3f} ms\n")
        self.output_text.insert(tk.END, f"Tìm thấy {len(results)} trạm:\n")
        self.output_text.insert(tk.END, "-"*100 + "\n")
        for i, (point, dist) in enumerate(results, 1):
            data = point.data
            self.output_text.insert(tk.END,
                f"{i}. {data.get('name', 'N/A')} ({data.get('brand', 'N/A')})\n"
                f"   Địa chỉ: {data.get('display_name', 'N/A')}\n"
                f"   Khoảng cách: {dist:.2f} km\n"
                f"   Tọa độ: ({point.lat:.6f}, {point.lon:.6f})\n\n")
        self.output_text.see(tk.END)

        # Vẽ hình vuông (đỏ để phân biệt)
        self.add_result_markers(results, lat, lon, r, is_rtree=True)

if __name__ == "__main__":
    app = App()
    app.mainloop()