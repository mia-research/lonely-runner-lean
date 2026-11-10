#!/bin/sh
# E833: rerun, with saved outputs, the chain of certifiers that closes rho7 in [25,41): fixed-R0 boxes (C, frontier_box_dfs_v1.c; outputs frontier_box_dfs_v1_*.out and the leaf files), then the window-type certifier on the leaves, then the plane-split certifier.
cd "$(dirname "$0")"
for r in 29_31 31_33 33_35 35_37 39_41; do
  python3 frontier_window_cert_v1.py frontier_box_dfs_v1_leaves64_$r.txt 64  > frontier_close_win64_$r.out
done
for r in 29_31 31_33 33_35 39_41; do
  python3 frontier_window_cert_v1.py frontier_box_dfs_v1_leaves64_$r.txt 256 > frontier_close_win256_$r.out
done
for r in 29_31 31_33 33_35; do
  python3 frontier_window_cert_v1.py frontier_box_dfs_v1_leaves64_${r}_wleaves_256.txt 1024 > frontier_close_win1024_$r.out
done
python3 frontier_plane_cert_v1.py frontier_box_dfs_v1_leaves64_35_37_wleaves_64.txt 128 > frontier_close_plane128_35_37.out
