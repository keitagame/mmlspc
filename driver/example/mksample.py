#!/usr/bin/env python3
"""テスト用 BRR サンプルとサンプルディレクトリを生成する。
o4c(261.6Hz) が ピッチ値 $1000 (=32kHz 等速再生) で鳴るよう、
368 サンプル(23 ブロック)に正弦波 3 周期を入れてループさせる。
  sine.brr   ... ループ付き BRR (配置先 $4000)
  dir.bin    ... サンプルディレクトリ (配置先 $1F00)  音色0 = $4000
"""
import math, struct

N, PERIODS = 368, 3
wave = [int(12000 * math.sin(2 * math.pi * PERIODS * i / N)) for i in range(N)]

out = bytearray()
for b in range(N // 16):
    blk = wave[b * 16:(b + 1) * 16]
    for r in range(13):                      # 範囲 0..12 から収まる最小を選ぶ
        ns = [round(2 * x / (1 << r)) for x in blk]
        if all(-8 <= n <= 7 for n in ns):
            break
    last = (b == N // 16 - 1)
    out.append((r << 4) | (0b11 if last else 0))   # フィルタ0, 最終ブロックは end+loop
    for i in range(0, 16, 2):
        out.append(((ns[i] & 15) << 4) | (ns[i + 1] & 15))

open("sine.brr", "wb").write(out)
open("dir.bin", "wb").write(struct.pack("<HH", 0x4000, 0x4000))
print("sine.brr", len(out), "bytes")
