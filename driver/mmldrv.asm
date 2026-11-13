; ============================================================
;  mmldrv — mmlc 用の最小 SPC700 サウンドドライバ (8ch)
;
;  assemble:  asar mmldrv.asm mmldrv.bin
;  配置:      $0200 (mmldrv.drv の load で配置)
;  曲データ:  $2000 (先頭に 8 本のトラックポインタ表(word) )
;
;  イベント形式 (mmldrv.drv と対応)
;    $00-$7F  pitch len     ノート。pitch = o*12+半音 (o4c = $30 = 原音)
;    $80                    トラック終端(以後そのチャンネルは停止)
;    $81 lo hi              ジャンプ (ループ)
;    $82 n                  テンポ: タイマー0の分周値 (= 10000/BPM)
;    $83 n                  音色 (SRCN)
;    $84 n                  音量 0-127
;    $85 n                  パン 0-127 (0=左 64=中央 127=右)
;    $86 n                  ゲート: ノート末尾 n tick を離鍵(0=レガート)
;    $C8 len                タイ(前の音を延長)
;    $C9 len                休符(離鍵して待つ)
; ============================================================
norom
arch spc700
org $0000
base $0200

; ---- zero page ------------------------------------------------
!cur      = $00      ; word  : 現在のトラックポインタ
!tmp      = $02
!oct      = $03
!pl       = $04
!ph       = $05
!vbase    = $06      ; DSP ボイスレジスタ基点 (voice*16)
!ticks    = $07
!chmask   = $08
!konmask  = $09
!koffmask = $0A

; チャンネル別配列。添字 X = ch*2 (0,2,..14) 。各 16 バイト
!ptrL     = $20
!ptrH     = $30
!cnt      = $40
!gate     = $50
!vol      = $60
!pan      = $70
!inst     = $80

; ---- hardware -------------------------------------------------
!DSPADDR  = $F2
!DSPDATA  = $F3
!CONTROL  = $F1
!T0TARGET = $FA
!T0OUT    = $FD

!SONG     = $2000
!DEFTEMPO = 83       ; 10000/120

; ============================================================
start:
    clrp
    mov   x,#$EF
    mov   sp,x

    mov   a,#$00             ; zero page クリア
    mov   x,#$EE
-   mov   $00+x,a
    dec   x
    bne   -
    mov   $00,a

    mov   x,#$00             ; DSP 初期化
-   mov   a,dsptab+x
    mov   y,a
    mov   a,dsptab+1+x
    call  dw
    inc   x
    inc   x
    cmp   x,#(dsptab_end-dsptab)
    bne   -

    mov   x,#$00             ; トラック初期化
-   mov   a,!SONG+x
    mov   !ptrL+x,a
    mov   a,!SONG+1+x
    mov   !ptrH+x,a
    mov   a,#$01
    mov   !cnt+x,a
    mov   a,#100
    mov   !vol+x,a
    mov   a,#64
    mov   !pan+x,a
    inc   x
    inc   x
    cmp   x,#16
    bne   -

    mov   !T0TARGET,#!DEFTEMPO
    mov   !CONTROL,#$01      ; タイマー0開始

mainloop:
    mov   a,!T0OUT
    beq   mainloop
    mov   !ticks,a
-   call  tick
    dec   !ticks
    bne   -
    bra   mainloop

; ============================================================
; 1 tick 分の処理
; ============================================================
tick:
    mov   y,#$5C             ; KOFF を解除
    mov   a,#$00
    call  dw
    mov   !konmask,a
    mov   !koffmask,a
    mov   !chmask,#$01
    mov   x,#$00

.chan:
    mov   a,!ptrH+x
    beq   .next              ; 停止中
    dec   !cnt+x
    bne   .waiting
    call  fetch
    bra   .next
.waiting:
    mov   a,!gate+x
    beq   .next
    cmp   a,!cnt+x
    bne   .next
    mov   a,!chmask          ; ゲート: 離鍵
    or    a,!koffmask
    mov   !koffmask,a
.next:
    asl   !chmask
    inc   x
    inc   x
    cmp   x,#16
    bne   .chan

    mov   y,#$5C             ; まとめて DSP へ
    mov   a,!koffmask
    call  dw
    mov   y,#$4C
    mov   a,!konmask
    call  dw
    ret

; ============================================================
; DSP 書き込み: Y = レジスタ, A = 値
; ============================================================
dw:
    mov   !DSPADDR,y
    mov   !DSPDATA,a
    ret

; トラックから 1 バイト読む (A)
rd:
    mov   y,#$00
    mov   a,(!cur)+y
    incw  !cur
    ret

; ============================================================
; イベント取得 (X = ch*2 を保持)
; ============================================================
fetch:
    mov   a,!ptrL+x
    mov   !cur,a
    mov   a,!ptrH+x
    mov   !cur+1,a

.again:
    call  rd
    cmp   a,#$80
    bcs   .cmd
    jmp   note

.cmd:
    cmp   a,#$C8
    beq   .tie
    cmp   a,#$C9
    beq   .rest
    cmp   a,#$80
    beq   .end
    cmp   a,#$81
    beq   .jump
    cmp   a,#$82
    beq   .tempo
    cmp   a,#$83
    beq   .inst
    cmp   a,#$84
    beq   .vol
    cmp   a,#$85
    beq   .pan
    cmp   a,#$86
    beq   .gate
    ; 未知のコマンドは終端扱い
.end:
    mov   a,#$00
    mov   !ptrH+x,a
    mov   a,!chmask
    or    a,!koffmask
    mov   !koffmask,a
    ret

.tie:
    call  rd
    mov   !cnt+x,a
    jmp   save

.rest:
    call  rd
    mov   !cnt+x,a
    mov   a,!chmask
    or    a,!koffmask
    mov   !koffmask,a
    jmp   save

.jump:
    call  rd
    mov   !tmp,a
    call  rd
    mov   !cur+1,a
    mov   a,!tmp
    mov   !cur,a
    jmp   .again

.tempo:
    call  rd
    mov   !T0TARGET,a
    jmp   .again
.inst:
    call  rd
    mov   !inst+x,a
    jmp   .again
.vol:
    call  rd
    mov   !vol+x,a
    jmp   .again
.pan:
    call  rd
    mov   !pan+x,a
    jmp   .again
.gate:
    call  rd
    mov   !gate+x,a
    jmp   .again

save:
    mov   a,!cur
    mov   !ptrL+x,a
    mov   a,!cur+1
    mov   !ptrH+x,a
    ret

; ============================================================
; ノートオン  A = pitch (0-71)
; ============================================================
note:
    mov   !tmp,a
    call  rd
    mov   !cnt+x,a

    mov   a,x                ; voice*16
    asl   a
    asl   a
    asl   a
    mov   !vbase,a

    mov   a,!tmp             ; A = オクターブ, Y = 半音
    mov   y,#$00
    push  x
    mov   x,#12
    div   ya,x
    pop   x
    mov   !oct,a
    mov   a,y
    asl   a
    mov   y,a
    mov   a,pitchtab+y
    mov   !pl,a
    mov   a,pitchtab+1+y
    mov   !ph,a

    mov   a,#5               ; テーブルは o5 の値。(5-oct) 回右シフト
    setc
    sbc   a,!oct
    beq   .shifted
    mov   y,a
-   lsr   !ph
    ror   !pl
    dec   y
    bne   -
.shifted:

    mov   a,!vbase           ; PITCH L/H
    or    a,#$02
    mov   y,a
    mov   a,!pl
    call  dw
    mov   a,!vbase
    or    a,#$03
    mov   y,a
    mov   a,!ph
    call  dw

    mov   a,!vbase           ; SRCN
    or    a,#$04
    mov   y,a
    mov   a,!inst+x
    call  dw

    mov   a,#127             ; VOL L = vol*(127-pan)>>7
    setc
    sbc   a,!pan+x
    mov   y,!vol+x
    mul   ya
    asl   a
    mov   a,y
    rol   a
    mov   !tmp,a
    mov   a,!vbase
    mov   y,a
    mov   a,!tmp
    call  dw

    mov   a,!pan+x           ; VOL R = vol*pan>>7
    mov   y,!vol+x
    mul   ya
    asl   a
    mov   a,y
    rol   a
    mov   !tmp,a
    mov   a,!vbase
    or    a,#$01
    mov   y,a
    mov   a,!tmp
    call  dw

    mov   a,!chmask          ; KON 予約
    or    a,!konmask
    mov   !konmask,a
    jmp   save

; ============================================================
; テーブル
; ============================================================
dsptab:
    db $0C,$7F, $1C,$7F      ; MVOL L/R
    db $2C,$00, $3C,$00      ; EVOL L/R
    db $0D,$00               ; EFB
    db $2D,$00, $3D,$00, $4D,$00   ; PMON NON EON
    db $5C,$00, $4C,$00      ; KOFF KON
    db $6C,$20               ; FLG (mute off, echo write off)
dsptab_end:

; o5 (pitch 60-71) のピッチ値  0x1000 * 2^((p-48)/12)
pitchtab:
    dw $2000,$21E7,$23EB,$260E,$2851,$2AB7,$2D41,$2FF2,$32CC,$35D1,$3904,$3C68
