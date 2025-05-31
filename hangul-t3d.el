;; -*- lexical-binding: t -*-
;; hangul-t3d.el --- Korean Hangul input method, Tark Sebulshik

;; Author: Kyoung-Tark Kim(김경탁), kyoungtarkkim@gmail.com
;; Keywords: multilingual, input method, Korean, Hangul, Tark Sebulshik D
;; Version: 1.00 (Apr. 14, 2025)

;; The major portions of this code are modified or derived from `hangul.el'.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.


;; Commentary:
;; The goal of this code is to implement a new Hangul input method into Emacs
;; using the following automata:
;; Hangul Tark Sebulshik D (탁 세벌식D).


;; In this code, `key', `char', and `charx' refer to:
;; 1. key: ASCII code (from 0 to 127) provided by Emacs input.
;; 2. char: Hangul Jamo index.
;; 3. charx: Unicode for Hangul Jamo.
;; For `char' and `charx', see the table of Hangul Jamo indices below (Table 1).
;; For the printable ASCII codes (from 33 to 126) see the Table 2 below.

;; If you find any improvements or errors in this code,
;; I would appreciate it if you could email me (to: kyoungtarkkim@gmail.com).


;; Code:

(require 'quail)
(require 'hanja-util)

;; Table 1. The Hangul Jamo indicies and Unicodes
;; +------------+------------+------------+------------+
;; | Base index | cho (+0)   |jung (+100) |jong (+1000)|
;; +------------+------------+------------+------------+
;;   1            ᄀ ?\x1100    ᅡ ?\x1161   ᆨ ?\x11a8  
;;   2            ᄁ ?\x1101    ᅢ ?\x1162   ᆩ ?\x11a9  
;;   3            ᄂ ?\x1102    ᅣ ?\x1163   ᆪ ?\x11aa  
;;   4            ᄃ ?\x1103    ᅤ ?\x1164   ᆫ ?\x11ab  
;;   5            ᄄ ?\x1104    ᅥ ?\x1165   ᆬ ?\x11ac  
;;   6            ᄅ ?\x1105    ᅦ ?\x1166   ᆭ ?\x11ad  
;;   7            ᄆ ?\x1106    ᅧ ?\x1167   ᆮ ?\x11ae  
;;   8            ᄇ ?\x1107    ᅨ ?\x1168   ᆯ ?\x11af  
;;   9            ᄈ ?\x1108    ᅩ ?\x1169   ᆰ ?\x11b0  
;;   10           ᄉ ?\x1109    ᅪ ?\x116a   ᆱ ?\x11b1  
;;   11           ᄊ ?\x110a    ᅫ ?\x116b   ᆲ ?\x11b2  
;;   12           ᄋ ?\x110b    ᅬ ?\x116c   ᆳ ?\x11b3  
;;   13           ᄌ ?\x110c    ᅭ ?\x116d   ᆴ ?\x11b4  
;;   14           ᄍ ?\x110d    ᅮ ?\x116e   ᆵ ?\x11b5  
;;   15           ᄎ ?\x110e    ᅯ ?\x116f   ᆶ ?\x11b6  
;;   16           ᄏ ?\x110f    ᅰ ?\x1170   ᆷ ?\x11b7  
;;   17           ᄐ ?\x1110    ᅱ ?\x1171   ᆸ ?\x11b8  
;;   18           ᄑ ?\x1111    ᅲ ?\x1172   ᆹ ?\x11b9  
;;   19           ᄒ ?\x1112    ᅳ ?\x1173   ᆺ ?\x11ba  
;;   20                        ᅴ ?\x1174   ᆻ ?\x11bb  
;;   21                        ᅵ ?\x1175   ᆼ ?\x11bc  
;;   22                                     ᆽ ?\x11bd  
;;   23                                     ᆾ ?\x11be  
;;   24                                     ᆿ ?\x11bf  
;;   25                                     ᇀ ?\x11c0  
;;   26                                     ᇁ ?\x11c1  
;;   27                                     ᇂ ?\x11c2  
;; +------------+------------+------------+------------+
;; Thus, there are a total of 19 * 21 * (27 +1) = 11,172 modern Hangul syllables.
;; The Unicode formula for Hangul combination is:
;; Hangul unicode = #xac00 + (21*28* (cho_index -1)) + (28* (jung_index -101))
;;                         + (jong_index -1000)
;; e.g., 힣's unicode = ?\xd7a3 = ?\xac00 + (588* 18) + (28* 20) + 27
;; Note: ㅎ(cho),ㅣ(jung),ㅎ(jong) have indices 19, 121, and 1027, respectively.
;;       (These indices are not standard; they are temporarily assigned by me.)


;; The combination rule for choseong in hangul-t3d is:
;; ㄲ=ㄱ(k)+ㄱ(k)=ㄱ(k)+ㅇ(j)=ㅇ(j)+ㄱ(k)
;; ㅋ=ㄱ(k)+ㅎ(h)=ㅎ(h)+ㄱ(k)
;; ㄸ=ㄷ(i)+ㄷ(i)=ㄷ(i)+ㅇ(j)=ㅇ(j)+ㄷ(i)
;; ㅌ=ㄷ(i)+ㅎ(h)=ㅎ(h)+ㄷ(i)
;; ㅃ=ㅂ(o)+ㅂ(o)=ㅂ(o)+ㅇ(j)=ㅇ(j)+ㅂ(o)
;; ㅍ=ㅂ(o)+ㅎ(h)=ㅎ(h)+ㅂ(o)
;; ㅆ=ㅅ(n)+ㅅ(n)=ㅅ(n)+ㅇ(j)=ㅇ(j)+ㅅ(n)
;; ㅈ=ㅈ(l)+ㅈ(l)=ㅈ(l)+ㅇ(j)=ㅇ(j)+ㅈ(l)
;; ㅊ=ㅈ(l)+ㅎ(h)=ㅎ(h)+ㅈ(l)












;; Table 2. Printable ASCII codes (from 32 to 126)
;; Note that 32 (?\x20) is a space, namely " ", so omitted.
;;  +-------+-------+-------+
;;  |  Dec  |  Hex  | Text  |
;;  +-------+-------+-------+
;;  |  33   | ?\x21 |   !   |
;;  |  34   | ?\x22 |   "   |
;;  |  35   | ?\x23 |   #   |
;;  |  36   | ?\x24 |   $   |
;;  |  37   | ?\x25 |   %   |
;;  |  38   | ?\x26 |   &   |
;;  |  39   | ?\x27 |   '   |
;;  |  40   | ?\x28 |   (   |
;;  |  41   | ?\x29 |   )   |
;;  |  42   | ?\x2a |   *   |
;;  |  43   | ?\x2b |   +   |
;;  |  44   | ?\x2c |   ,   |
;;  |  45   | ?\x2d |   -   |
;;  |  46   | ?\x2e |   .   |
;;  |  47   | ?\x2f |   /   |
;;  |  48   | ?\x30 |   0   |
;;  |  49   | ?\x31 |   1   |
;;  |  50   | ?\x32 |   2   |
;;  |  51   | ?\x33 |   3   |
;;  |  52   | ?\x34 |   4   |
;;  |  53   | ?\x35 |   5   |
;;  |  54   | ?\x36 |   6   |
;;  |  55   | ?\x37 |   7   |
;;  |  56   | ?\x38 |   8   |
;;  |  57   | ?\x39 |   9   |
;;  |  58   | ?\x3a |   :   |
;;  |  59   | ?\x3b |   ;   |
;;  |  60   | ?\x3c |   <   |
;;  |  61   | ?\x3d |   =   |
;;  |  62   | ?\x3e |   >   |
;;  |  63   | ?\x3f |   ?   |
;;  |  64   | ?\x40 |   @   |
;;  |  65   | ?\x41 |   A   |
;;  |  66   | ?\x42 |   B   |
;;  |  67   | ?\x43 |   C   |
;;  |  68   | ?\x44 |   D   |
;;  |  69   | ?\x45 |   E   |
;;  |  70   | ?\x46 |   F   |
;;  |  71   | ?\x47 |   G   |
;;  |  72   | ?\x48 |   H   |
;;  |  73   | ?\x49 |   I   |
;;  |  74   | ?\x4a |   J   |
;;  |  75   | ?\x4b |   K   |
;;  |  76   | ?\x4c |   L   |
;;  |  77   | ?\x4d |   M   |
;;  |  78   | ?\x4e |   N   |
;;  |  79   | ?\x4f |   O   |
;;  |  80   | ?\x50 |   P   |
;;  |  81   | ?\x51 |   Q   |
;;  |  82   | ?\x52 |   R   |
;;  |  83   | ?\x53 |   S   |
;;  |  84   | ?\x54 |   T   |
;;  |  85   | ?\x55 |   U   |
;;  |  86   | ?\x56 |   V   |
;;  |  87   | ?\x57 |   W   |
;;  |  88   | ?\x58 |   X   |
;;  |  89   | ?\x59 |   Y   |
;;  |  90   | ?\x5a |   Z   |
;;  |  91   | ?\x5b |   [   |
;;  |  92   | ?\x5c |   \   |
;;  |  93   | ?\x5d |   ]   |
;;  |  94   | ?\x5e |   ^   |
;;  |  95   | ?\x5f |   _   |
;;  |  96   | ?\x60 |   `   |
;;  |  97   | ?\x61 |   a   |
;;  |  98   | ?\x62 |   b   |
;;  |  99   | ?\x63 |   c   |
;;  | 100   | ?\x64 |   d   |
;;  | 101   | ?\x65 |   e   |
;;  | 102   | ?\x66 |   f   |
;;  | 103   | ?\x67 |   g   |
;;  | 104   | ?\x68 |   h   |
;;  | 105   | ?\x69 |   i   |
;;  | 106   | ?\x6a |   j   |
;;  | 107   | ?\x6b |   k   |
;;  | 108   | ?\x6c |   l   |
;;  | 109   | ?\x6d |   m   |
;;  | 110   | ?\x6e |   n   |
;;  | 111   | ?\x6f |   o   |
;;  | 112   | ?\x70 |   p   |
;;  | 113   | ?\x71 |   q   |
;;  | 114   | ?\x72 |   r   |
;;  | 115   | ?\x73 |   s   |
;;  | 116   | ?\x74 |   t   |
;;  | 117   | ?\x75 |   u   |
;;  | 118   | ?\x76 |   v   |
;;  | 119   | ?\x77 |   w   |
;;  | 120   | ?\x78 |   x   |
;;  | 121   | ?\x79 |   y   |
;;  | 122   | ?\x7a |   z   |
;;  | 123   | ?\x7b |   {   |
;;  | 124   | ?\x7c |   |   |
;;  | 125   | ?\x7d |   }   |
;;  | 126   | ?\x7e |   ~   |
;;  +-------+-------+-------+


;; A convenient array of printable ASCII codes (from 33 to 126) is as follows:

;; ! " # $ % & ' ( ) * + , - . /                         (15개)
;; 0 1 2 3 4 5 6 7 8 9                                   (10개)
;; : ; < = > ? @                                          (7개)
;; A B C D E F G H I J K L M N O P Q R S T U V W X Y Z   (26개)
;; [ \ ] ^ _ `                                            (6개)
;; a b c d e f g h i j k l m n o p q r s t u v w x y z   (26개)
;; { | } ~                                                (4개)


;; hangul-t3d keymap.
;; The reason for using Hangul Jamo Unicode (U+1100–U+11FF) in the keymap
;; is simply because choseong, jungseong, and jongseong of Hangul syllable
;; are separated, and there exists a convenient formula for combining them into
;; complete Hangul Characters Unicodes.
(defconst hangul-t3d-keymap
 [?\x21 ?\x22 ?\x23 ?\x24 ?\x25 ?\x26 ?\x1110 ?\x28 ?\x29 ?\x2a ?\x2b ?\x2c ?\x2d ?\x2e ?\x110f

   ?\x30 ?\x31 ?\x32 ?\x33 ?\x34 ?\x35 ?\x36 ?\x37 ?\x38 ?\x39

   ?\x3a ?\x1107 ?\x3c ?\x3d ?\x3e ?\x3f ?\x40

   ?\x2018 ?\x2190 ?\x300a ?\x201c ?\x300e ?\x201d ?\x25cb ?\x2715 ;; ABCDEFGH
   ?\xb7 ?\x3b ?\x27 ?\x2015 ?\x2f ?\x2192 ?\x203b ?\xb7           ;; IJKLMNOP
   ?\x300c ?\x300f ?\x2019 ?\x25b3 ?\x22ef ?\x300b ?\x300d ?\x3009 ;; QRSTUVWX
   ?\x25a1 ?\x3008                                                 ;; YZ

   ?\x5b ?\x5c ?\x5d ?\x5e ?\x5f ?\x60

   [?\x1162 ?\x11b7 ?\x1162] ?\C-g                                  ;; ab
   [?\x1173 ?\x11c2 ?\x11c2] [?\x1175 ?\x11bc ?\x1175]              ;; cd
   [?\x1166 ?\x11a8 ?\x1166] [?\x1161 ?\x11be ?\x1161]              ;; ef
   ?\x1169                                                          ;; g

   ?\x1112 ?\x1103 ?\x110b ?\x1100 ?\x110c ?\x1105 ?\x1109 ?\x110e ?\x1111
                                                                    ;; hijklmnop

   [?\x1172 ?\x11c1 ?\x11c1] [?\x116e ?\x11bb ?\x116e] ;; qr
   [?\x116d ?\x11ab ?\x11ab] ?\x1167                   ;; st
   ?\x1102                                             ;; u
   [?\x1165 ?\x11bf ?\x1165] [?\x1168 ?\x11af ?\x11af] ;; vw
   [?\x1164 ?\x11ba ?\x11ba]                           ;; x
   ?\x1106                                             ;; y
   [?\x1163 ?\x11b8 ?\x11b8]                           ;; z

   ?\x7b ?\x7c ?\x7d ?\x7e])



(defvar hangul-t3d-im-keymap
  (let ((map (make-sparse-keymap)))
    (define-key map "\d" #'hangul-t3d-delete-backward-char)
    (define-key map [f9] #'hangul-t3d-to-hanja-conversion)
    (define-key map [Hangul_Hanja] #'hangul-to-hanja-conversion)
    map)
  "Keymap for Hangul method.  It is used by all Hangul input methods.")



;; In the original `hangul.el', the vector `HANGUL-QUEUE' has a length of 6.
;; However, in our version, the queue vector has length 3, meaning:
;; `cho' has 1 component at position 0;
;; `jung' has 1 component at positions 1;;; `jong' has 1 component at position 2.
;; NOTE: The number 3 represents the number of unit determined by deleting JASO
;;       using the backspace key.
(defvar hangul-t3d-queue
  (make-vector 3 0))

;; The following variable is necessary for implementing jungseong and jongseong alternation (so called, `申세벌식_첫가끝_갈마들이') in hangul-t3d.
(defvar hangul-t3d-galma-mode 0
  "0 means moeum mode, 1 means jaeum mode, and 2 means b-combination mode.")


;; Beware: We do NOT use Unicode #x1100-#x11FF for printing choseong, jungseong,
;;         and jongseong. This is because these Unicode characters are large,
;;         making them unsuitable for printing. Instead, we use the smaller Hangul
;;         Compatibility Jamo Unicode characters for printing.
;; Example: Compare the sizes of ?\x1100 = ᄀ and ?\x3131 = ㄱ.

;; Table 3. Hangul Compatibility Jamo (i.e., Jaeum, Moeum)
;; +------------+------------+------------+
;; | Index      | Consonants |   Vowels   |
;; +------------+------------+------------+
;;   1            ㄱ ?\x3131    ㅏ ?\x314f
;;   2            ㄲ ?\x3132    ㅐ ?\x3150
;;   3            ㄳ ?\x3133    ㅑ ?\x3151
;;   4            ㄴ ?\x3134    ㅒ ?\x3152
;;   5            ㄵ ?\x3135    ㅓ ?\x3153
;;   6            ㄶ ?\x3136    ㅔ ?\x3154
;;   7            ㄷ ?\x3137    ㅕ ?\x3155
;;   8            ㄸ ?\x3138    ㅖ ?\x3156
;;   9            ㄹ ?\x3139    ㅗ ?\x3157
;;   10           ㄺ ?\x313a    ㅘ ?\x3158
;;   11           ㄻ ?\x313b    ㅙ ?\x3159
;;   12           ㄼ ?\x313c    ㅚ ?\x315a
;;   13           ㄽ ?\x313d    ㅛ ?\x315b
;;   14           ㄾ ?\x313e    ㅜ ?\x315c
;;   15           ㄿ ?\x313f    ㅝ ?\x315d
;;   16           ㅀ ?\x3140    ㅞ ?\x315e
;;   17           ㅁ ?\x3141    ㅟ ?\x315f
;;   18           ㅂ ?\x3142    ㅠ ?\x3160
;;   19           ㅃ ?\x3143    ㅡ ?\x3161
;;   20           ㅄ ?\x3144    ㅢ ?\x3162
;;   21           ㅅ ?\x3145    ㅣ ?\x3163
;;   22           ㅆ ?\x3146
;;   23           ㅇ ?\x3147
;;   24           ㅈ ?\x3148
;;   25           ㅉ ?\x3149
;;   26           ㅊ ?\x314a
;;   27           ㅋ ?\x314b
;;   28           ㅌ ?\x314c
;;   29           ㅍ ?\x314d
;;   30           ㅎ ?\x314e
;; +------------+------------+------------+
(defun hangul-t3d-character (cho jung jong)
  "Convert CHO, JUNG, JONG to the precomposed `Hangul_Syllables' character.
Return a zero-length string if the conversion fails."
  (or
   (decode-char 'ucs
                (if (and (/= cho 0) (/= jung 0))
                    (+ #xac00
                       (* 588 (1- cho))
                       (* 28 (- jung 101))
                       (cond
                        ((/= jong 0) (- jong 1000))
                        (t 0)))
                  (+ #x3130
	                 (cond ((/= cho 0) (+ cho
                                          (cond ((<= cho 2) 0)
                                                ((<= cho 3) 1)
                                                ((<= cho 6) 3)
                                                ((<= cho 9) 10)
                                                (t 11))))
	                       ((/= jung 0) (+ (- jung 100) #x1e))
	                       ((/= jong 0) (+ (- jong 1000)
                                           (cond ((<= jong 1007) 0)
                                                 ((<= jong 1017) 1)
                                                 ((<= jong 1022) 2)
                                                 (t 3))))))))
   ""))




;; Note: As will become clear, the parameter `queues' consists of either
;;       one queue or two queues (and never more than two queues).
(defun hangul-t3d-insert-character (&rest queues)
  "Insert characters generated from QUEUES.
Each queue in QUEUES has the same form as `hangul-t3d-queue'.
Setup `quail-overlay' to the last character."
  (if (and mark-active transient-mark-mode)
      (progn
        (delete-region (region-beginning) (region-end))
        (deactivate-mark)))
  (quail-delete-region)
  (let ((first (car queues)))
    (insert (hangul-t3d-character
             (aref first 0)
             (aref first 1)
             (aref first 2))))
  (move-overlay quail-overlay (overlay-start quail-overlay) (point))
  (dolist (queue (cdr queues))
    (insert (hangul-t3d-character
             (aref queue 0)
             (aref queue 1)
             (aref queue 2)))
    (move-overlay quail-overlay (1+ (overlay-start quail-overlay)) (point))))




(defun hangul-t3d-djamo (char1 char2)
  "Return the double Jamo index calculated from the arguments.
CHAR1 and CHAR2 are Hangul Jamo indices.
Return CHAR1 if CHAR1 and CHAR2 can not be combined."
  (cond
   ;; choseong
   ((= char1 1) (cond
                 ((= char2 1) 2)
                 ((= char2 10) 1003)
                 ((= char2 12) 2)
                 ((= char2 19) 16)
                 (t char1)))
   ((= char1 3) (cond
                 ((= char2 13) 1005)
                 ((= char2 19) 1006)
                 (t char1)))
   ((= char1 4) (cond
                 ((= char2 4) 5)
                 ((= char2 12) 5)
                 ((= char2 19) 17)
                 (t char1)))
   ((= char1 6) (cond
                 ((= char2 1) 1009)
                 ((= char2 7) 1010)
                 ((= char2 8) 1011)
                 ((= char2 10) 1012)
                 ((= char2 19) 1015)
                 (t char1)))
   ((= char1 8) (cond
                 ((= char2 8) 9)
                 ((= char2 10) 1018)
                 ((= char2 12) 9)
                 ((= char2 19) 18)
                 (t char1)))
   ((= char1 10) (cond
                  ((= char2 10) 11)
                  ((= char2 12) 11)
                  (t char1)))
   ((= char1 12) (cond
                  ((= char2 1) 2)
                  ((= char2 4) 5)
                  ((= char2 8) 9)
                  ((= char2 10) 11)
                  ((= char2 13) 14)
                  (t char1)))
   ((= char1 13) (cond
                  ((= char2 12) 14)
                  ((= char2 13) 14)
                  ((= char2 19) 15)
                  (t char1)))
   ((= char1 17) (cond
                  ((= char2 6) 1013)
                  (t char1)))
   ((= char1 18) (cond
                  ((= char2 6) 1014)
                  (t char1)))
   ((= char1 19) (cond
                  ((= char2 1) 16)
                  ((= char2 4) 17)
                  ((= char2 8) 18)
                  ((= char2 13) 15)
                  (t char1)))

   ;; jungseong
   ((= char1 109) (cond
                   ((= char2 101) 110)
                   ((= char2 102) 111)
                   ((= char2 121) 112)
                   (t char1)))
   ((= char1 114) (cond
                   ((= char2 105) 115)
                   ((= char2 106) 116)
                   ((= char2 121) 117)
                   (t char1)))
   ((= char1 119) (cond
                   ((= char2 101) 110)
                   ((= char2 102) 111)

                   ((= char2 105) 115)
                   ((= char2 106) 116)

                   ((= char2 109) 112)
                   ((= char2 114) 117)

                   ((= char2 121) 120)

                   (t char1)))


;; The combination rule for jongseong in hangul-t3d is:
;; /.


;; ㄲ=ㄱ(e)+ㄱ(e)           =ㄱ(e)+ㅁ(a)=ㅁ(a)+ㄱ(e)
;; ㄳ=ㄱ(e)+ㅅ(x)=ㅅ(x)+ㄱ(e)=ㄱ(e)+ㅆ(r)=ㅆ(r)+ㄱ(e)
;; ㄵ=ㄴ(s)+ㅈ(2)=ㅈ(2)+ㄴ(s)=ㄴ(s)+ㄱ(e)=ㄱ(e)+ㄴ(s)
;; ㄶ=ㄴ(s)+ㅎ(c)=ㅎ(c)+ㄴ(s)=ㄴ(s)+ㅇ(d)=ㅇ(d)+ㄴ(s)
;; ㄺ=ㄹ(w)+ㄱ(e)=ㄱ(d)+ㄹ(w)
;; ㄻ=ㄹ(w)+ㅁ(a)=ㅁ(a)+ㄹ(w)
;; ㄼ=ㄹ(w)+ㅂ(z)=ㅂ(z)+ㄹ(w)=ㅅ(x)+ㅎ(c)=ㅎ(c)+ㅅ(x)=ㅁ(a)+ㄴ(s)=ㄴ(s)+ㅁ(a)
;; ㄽ=ㄹ(w)+ㅅ(x)=ㅅ(x)+ㄹ(w)=ㄹ(w)+ㅆ(r)=ㅆ(r)+ㄹ(w)
;; ㄾ=ㄹ(w)+ㅌ(4)=ㅌ(4)+ㄹ(w)
;; ㄿ=ㄹ(w)+ㅍ(q)=ㅍ(q)+ㄹ(w)
;; ㅀ=ㄹ(w)+ㅎ(c)=ㅎ(c)+ㄹ(w)=ㄹ(w)+ㅇ(d)=ㅇ(d)+ㄹ(w)=ㄴ(s)+ㅂ(z)=ㅂ(z)+ㄴ(s)
;; ㅄ=ㅂ(z)+ㅅ(x)=ㅅ(x)+ㅂ(z)



   ((= char1 1001) (cond
                    ((= char2 1001) 1002)
                    ((= char2 1004) 1005)
                    ((= char2 1008) 1009)
                    ((= char2 1016) 1002)
                    ((= char2 1019) 1003)
                    ((= char2 1020) 1003)
                    (t char1)))
   ((= char1 1004) (cond
                    ((= char2 1001) 1005)
                    ((= char2 1016) 1011)
                    ((= char2 1017) 1015)
                    ((= char2 1021) 1006)
                    ((= char2 1022) 1005)
                    ((= char2 1027) 1006)
                    (t char1)))
   ((= char1 1008) (cond
                    ((= char2 1001) 1009)
                    ((= char2 1016) 1010)
                    ((= char2 1017) 1011)
                    ((= char2 1019) 1012)
                    ((= char2 1020) 1012)
                    ((= char2 1021) 1015)
                    ((= char2 1025) 1013)
                    ((= char2 1026) 1014)
                    ((= char2 1027) 1015)
                    (t char1)))
   ((= char1 1016) (cond
                    ((= char2 1001) 1002)
                    ((= char2 1004) 1011)
                    ((= char2 1008) 1010)
                    (t char1)))
   ((= char1 1017) (cond
                    ((= char2 1004) 1015)
                    ((= char2 1008) 1011)
                    ((= char2 1019) 1018)
                    (t char1)))
   ((= char1 1019) (cond
                    ((= char2 1001) 1003)
                    ((= char2 1008) 1012)
                    ((= char2 1017) 1018)
                    ((= char2 1027) 1011)
                    (t char1)))
   ((= char1 1020) (cond
                    ((= char2 1001) 1003)
                    ((= char2 1008) 1012)
                    (t char1)))
   ((= char1 1021) (cond
                    ((= char2 1004) 1006)
                    ((= char2 1008) 1015)
                    (t char1)))
   ((= char1 1022) (cond
                    ((= char2 1004) 1005)
                    (t char1)))
   ((= char1 1025) (cond
                    ((= char2 1008) 1013)
                    (t char1)))
   ((= char1 1026) (cond
                    ((= char2 1008) 1014)
                    (t char1)))
   ((= char1 1027) (cond
                    ((= char2 1004) 1006)
                    ((= char2 1008) 1015)
                    ((= char2 1019) 1011)
                    (t char1)))

   (t char1)))




;; The following def-substitution is a combined version of
;; `hangul3-input-method-cho',
;; `hangul3-input-method-jung',
;; and `hangul3-input-method-jong'
;; in the original `hangul.el'.
(defsubst hangul-t3d-input-method-individual (char)
  "Store Hangul Jamo index CHAR in `hangul-t3d-queue' for choseong, jungseong,
 and jongseong."
  (cond

   ((and (>= char 1) (<= char 19))                          ;; for choseong
    (let (temp)
      (if (cond ((zerop (apply #'+ (append hangul-t3d-queue nil)))
                 (aset hangul-t3d-queue 0 char))
                ((and (zerop (aref hangul-t3d-queue 1))
                      (zerop (aref hangul-t3d-queue 2))
                      (/= (aref hangul-t3d-queue 0)
                          (setq temp (hangul-t3d-djamo
                                      (aref hangul-t3d-queue 0) char))))
                 (cond ((and (>= temp 1) (<= temp 19))
                        (aset hangul-t3d-queue 0 temp))
                       ((and (>= temp 1001) (<= temp 1027))
                        (aset hangul-t3d-queue 0 0)
                        (aset hangul-t3d-queue 1 0)
                        (aset hangul-t3d-queue 2 temp)))))
          (hangul-t3d-insert-character hangul-t3d-queue)
        (hangul-t3d-insert-character hangul-t3d-queue
			                         (setq hangul-t3d-queue (vector char 0 0))))))


   ((and (>= char 101) (<= char 121))                       ;; for jungseong
    (let (temp)
      (if (cond ((and (zerop (aref hangul-t3d-queue 1))
                      (zerop (aref hangul-t3d-queue 2)))
                 (aset hangul-t3d-queue 1 char))
                ((and (zerop (aref hangul-t3d-queue 2))
                      (/= (aref hangul-t3d-queue 1)
                          (setq temp (hangul-t3d-djamo
                                      (aref hangul-t3d-queue 1) char))))
                 (aset hangul-t3d-queue 1 temp)))
          (hangul-t3d-insert-character hangul-t3d-queue)
        (hangul-t3d-insert-character hangul-t3d-queue
			                        (setq hangul-t3d-queue (vector 0 char 0))))))


   ((and (>= char 1001) (<= char 1027))                     ;; for jongseong
    (let (temp)
      (if (cond ((and (zerop (aref hangul-t3d-queue 2))
                      (not (zerop (aref hangul-t3d-queue 0)))
                      (not (zerop (aref hangul-t3d-queue 1)))
                      (numberp (hangul-t3d-character (aref hangul-t3d-queue 0)
                                                    (aref hangul-t3d-queue 1)
                                                     char)))
                 (aset hangul-t3d-queue 2 char))
                ((and (not (zerop (aref hangul-t3d-queue 0)))
                      (not (zerop (aref hangul-t3d-queue 1)))
                      (/= (aref hangul-t3d-queue 2)
                          (setq temp (hangul-t3d-djamo
                                      (aref hangul-t3d-queue 2) char)))
                      (numberp (hangul-t3d-character (aref hangul-t3d-queue 0)
                                                    (aref hangul-t3d-queue 1)
                                                     temp)))
                 (aset hangul-t3d-queue 2 temp)))
          (hangul-t3d-insert-character hangul-t3d-queue)
        (if (zerop (apply #'+ (append hangul-t3d-queue nil)))
	        (hangul-t3d-insert-character (setq hangul-t3d-queue (vector 0 0 char)))
          (hangul-t3d-insert-character hangul-t3d-queue
			                           (setq hangul-t3d-queue (vector 0 0 char)))))))))




(defun hangul-t3d-delete-backward-char ()
  "Delete the previous hangul character by Jaso units."
  (interactive)
  (let ((i 2))
    (while (and (> i 0) (zerop (aref hangul-t3d-queue i)))
      (setq i (1- i)))
    (aset hangul-t3d-queue i 0)
    (cond
     ((<= i 1) (setq hangul-t3d-galma-mode 0))
     ((= i 2) (setq hangul-t3d-galma-mode 1))))
  (if (not (zerop (apply #'+ (append hangul-t3d-queue nil))))
      (hangul-t3d-insert-character hangul-t3d-queue)
    (setq hangul-t3d-galma-mode 0)
    (delete-char -1)))



(defun hangul-t3d-to-hanja-conversion ()
  "Convert the previous hangul character to the corresponding hanja character.
When a Korean input method is off, convert the following hangul character."
  (interactive)
  (let ((echo-keystrokes 0)
        delete-func
        hanja-character)
    (if (and (overlayp quail-overlay) (overlay-start quail-overlay))
        (progn
	      (setq hanja-character (hangul-to-hanja-char (preceding-char)))
	      (setq delete-func (lambda () (delete-char -1))))
      (setq hanja-character (hangul-to-hanja-char (following-char)))
      (setq delete-func (lambda () (delete-char 1))))
    (when hanja-character
      (funcall delete-func)
      (insert hanja-character)
      (setq hangul-t3d-queue (make-vector 3 0))
      (if (and (overlayp quail-overlay) (overlay-start quail-overlay))
	      (move-overlay quail-overlay (point) (point))))))




;; Support function for `hangul-t3d-input-method'. Actually, this
;; function handles the hangul-t3d. KEY is an entered key 
;; code (ASCII num.) used for looking up `hangul-t3d-keymap'."
(defun hangul-t3d-input-method-internal (key)
  (let ((charx (aref hangul-t3d-keymap (- key 33))))
    (if (vectorp charx) (setq charx (aref charx hangul-t3d-galma-mode)))

    (cond ((and (>= charx #x1100) (<= charx #x1112))        ;; choseong
           (cond

            ((and (= key ?u)
                  (zerop hangul-t3d-galma-mode)
                  (not (zerop (aref hangul-t3d-queue 0)))
                  (zerop (aref hangul-t3d-queue 1)))
             (setq hangul-t3d-galma-mode 1)
             (hangul-t3d-input-method-individual 120))    ;; ㅢ


            ((and (= key ?o)
                  (zerop hangul-t3d-galma-mode)
                  (not (zerop (aref hangul-t3d-queue 0)))
                  (zerop (aref hangul-t3d-queue 1)))
             (setq hangul-t3d-galma-mode 1)
             (hangul-t3d-input-method-individual 115))    ;; ㅝ

            ((and (= key ?p)
                  (zerop hangul-t3d-galma-mode)
                  (not (zerop (aref hangul-t3d-queue 0)))
                  (zerop (aref hangul-t3d-queue 1)))
             (setq hangul-t3d-galma-mode 1)
             (hangul-t3d-input-method-individual 117))    ;; ㅟ

              ((and (= key ?/)
                    (zerop hangul-t3d-galma-mode)
                    (not (zerop (aref hangul-t3d-queue 0)))
                    (zerop (aref hangul-t3d-queue 1)))
               (setq hangul-t3d-galma-mode 1)
               (hangul-t3d-input-method-individual 110))    ;; ㅘ


              ((and (= key ?\')
                    (zerop hangul-t3d-galma-mode)
                    (not (zerop (aref hangul-t3d-queue 0)))
                    (zerop (aref hangul-t3d-queue 1)))
               (setq hangul-t3d-galma-mode 2)
               (hangul-t3d-input-method-individual 119))    ;; ㅡ


            (t (setq hangul-t3d-galma-mode 0)
               (hangul-t3d-input-method-individual (- charx #x1100 -1)))))


          ((and (>= charx #x1161) (<= charx #x1175))        ;; jungseong
           (cond

              ((and (= key ?b)
                    (zerop hangul-t3d-galma-mode)
                    (not (zerop (aref hangul-t3d-queue 0)))
                    (zerop (aref hangul-t3d-queue 1)))
               (setq hangul-t3d-galma-mode 2)               ;; galma=mode 2 activ.
               (hangul-t3d-input-method-individual 119))    ;; ㅡ

              (t (if (zerop (aref hangul-t3d-queue 0))
                     (setq hangul-t3d-galma-mode 0)
                   (setq hangul-t3d-galma-mode 1))
                 (hangul-t3d-input-method-individual (- charx #x1161 -101)))))


          ((and (>= charx #x11a8) (<= charx #x11c2))        ;; jongseong
           (setq hangul-t3d-galma-mode 1)
           (hangul-t3d-input-method-individual (- charx #x11a8 -1001)))


          (t (cond

              ((and (= key ?2)
                    (not (zerop hangul-t3d-galma-mode))
                    (not (zerop (aref hangul-t3d-queue 0)))
                    (not (zerop (aref hangul-t3d-queue 1))))
               (hangul-t3d-input-method-individual 1022))   ;; ㅈ

              ((and (= key ?3)
                    (not (zerop hangul-t3d-galma-mode))
                    (not (zerop (aref hangul-t3d-queue 0)))
                    (not (zerop (aref hangul-t3d-queue 1)))
                    (zerop (aref hangul-t3d-queue 2)))
               (hangul-t3d-input-method-individual 1007))   ;; ㄷ

              ((and (= key ?4)
                    (not (zerop hangul-t3d-galma-mode))
                    (not (zerop (aref hangul-t3d-queue 0)))
                    (not (zerop (aref hangul-t3d-queue 1))))
               (hangul-t3d-input-method-individual 1025))   ;; ㅌ



              ;; ((and (= key ?8)
              ;;       (zerop hangul-t3d-galma-mode)
              ;;       (not (zerop (aref hangul-t3d-queue 0)))
              ;;       (zerop (aref hangul-t3d-queue 1)))
              ;;  (setq hangul-t3d-galma-mode 1)
              ;;  (hangul-t3d-input-method-individual 120))    ;; ㅢ

              ;; ((and (= key ?9)
              ;;       (zerop hangul-t3d-galma-mode)
              ;;       (not (zerop (aref hangul-t3d-queue 0)))
              ;;       (zerop (aref hangul-t3d-queue 1)))
              ;;  (setq hangul-t3d-galma-mode 2)               ;; galma=mode 2 activ.
              ;;  (hangul-t3d-input-method-individual 119))    ;; ㅡ






              ((and (= key ?\[)
                    (zerop hangul-t3d-galma-mode)
                    (not (zerop (aref hangul-t3d-queue 0)))
                    (zerop (aref hangul-t3d-queue 1)))
               (setq hangul-t3d-galma-mode 1)
               (hangul-t3d-input-method-individual 116))    ;; ㅞ


              ((and (= key ?,)
                    (zerop hangul-t3d-galma-mode)
                    (not (zerop (aref hangul-t3d-queue 0)))
                    (zerop (aref hangul-t3d-queue 1)))
               (setq hangul-t3d-galma-mode 1)
               (hangul-t3d-input-method-individual 111))    ;; ㅙ

              ((and (= key ?.)
                    (zerop hangul-t3d-galma-mode)
                    (not (zerop (aref hangul-t3d-queue 0)))
                    (zerop (aref hangul-t3d-queue 1)))
               (setq hangul-t3d-galma-mode 1)
               (hangul-t3d-input-method-individual 112))    ;; ㅚ



              (t (cond
                  ((= charx ?\C-g)                          ;; Shift + l
                   (call-interactively #'keyboard-quit))

                  (t (insert charx)))

                 (setq hangul-t3d-galma-mode 0)
                 (setq hangul-t3d-queue (make-vector 3 0))
                 (move-overlay quail-overlay (point) (point))))))))



(defun hangul-t3d-input-method (key)
  "hangul-t3d input method."
  (if (or buffer-read-only (< key 33) (>= key 127))
      (list key)
    (quail-setup-overlays nil)
    (let ((input-method-function nil)
	      (echo-keystrokes 0)
	      (help-char nil))
      (setq hangul-t3d-galma-mode 0)
      (setq hangul-t3d-queue (make-vector 3 0))
      (hangul-t3d-input-method-internal key)
      (unwind-protect
	      (catch 'exit-input-loop
	        (while t
	          (let* ((seq (read-key-sequence nil))
		             (cmd (lookup-key hangul-t3d-im-keymap seq))
		             key)
		        (cond ((and (stringp seq)
			                (= 1 (length seq))
			                (setq key (aref seq 0))
			                (and (>= key 33) (< key 127)))
		               (hangul-t3d-input-method-internal key))
		              ((commandp cmd)
		               (call-interactively cmd))
		              (t
                       (setq hangul-t3d-galma-mode 0)
		               (setq unread-command-events
                             (nconc (listify-key-sequence seq)
                                    unread-command-events))
		               (throw 'exit-input-loop nil))))))
	    (quail-delete-overlays)))))



;; Text shown by describe-input-method.  Set to a proper text by
;; hangul-input-method-activate.
(defvar-local hangul-t3d-input-method-help-text nil)


(defun hangul-t3d-input-method-activate (_input-method func help-text &rest _args)
  "Activate Hangul input method INPUT-METHOD.
FUNC is a function to handle input key.
HELP-TEXT is a text set in `hangul-t3d-input-method-help-text'."
  (setq deactivate-current-input-method-function #'hangul-t3d-input-method-deactivate
	describe-current-input-method-function #'hangul-t3d-input-method-help
	hangul-t3d-input-method-help-text help-text)
  (quail-delete-overlays)
  (if (eq (selected-window) (minibuffer-window))
      (add-hook 'minibuffer-exit-hook #'quail-exit-from-minibuffer))
  (setq-local input-method-function func))

(defun hangul-t3d-input-method-deactivate ()
  "Deactivate the current Hangul input method."
  (interactive)
  (unwind-protect
      (progn
        (quail-hide-guidance)
        (quail-delete-overlays)
        (setq describe-current-input-method-function nil))
    (kill-local-variable 'input-method-function)))

(defun hangul-t3d-input-method-help ()
  "Describe the current Hangul input method."
  (interactive)
  (with-output-to-temp-buffer "*Help*"
    (princ hangul-t3d-input-method-help-text)))



;; From old hangul.el
(defsubst symbol+ (&rest syms)
  "Concatenate symbols"
  (intern (mapconcat 'symbol-name syms "")))

;; From old hangul.el
(defmacro hangul-register-input-method (package-name language input-method-func package-title package-description package-help)
  "Define input method activate function, deactivate function, help function,
and register input method"
  (let ((activate-func (symbol+ input-method-func '-activate))
        (deactivate-func (symbol+ input-method-func '-deactivate))
        (help-func (symbol+ input-method-func '-help)))
    `(progn
       (defun ,activate-func (&optional arg)
         (if (and arg
                  (< (prefix-numeric-value arg) 0))
             (unwind-protect
                 (progn
                   (quail-hide-guidance)
                   (quail-delete-overlays)
                   (setq describe-current-input-method-function nil))
               (kill-local-variable 'input-method-function))
           (setq deactivate-current-input-method-function ',deactivate-func)
           (setq describe-current-input-method-function ',help-func)
           (quail-delete-overlays)
           (if (eq (selected-window) (minibuffer-window))
               (add-hook 'minibuffer-exit-hook 'quail-exit-from-minibuffer))
           (set (make-local-variable 'input-method-function)
                ',input-method-func)))
       (defun ,deactivate-func ()
         (interactive)
         (,activate-func -1))
       (defun ,help-func ()
         (interactive)
         (with-output-to-temp-buffer "*Help*"
           (princ ,package-help)))
       (register-input-method ,package-name
                              ,language
                              ',activate-func
                              ,package-title
                              ,package-description))))


(hangul-register-input-method
 "korean-hangul-t3d"
 "UTF-8"
 hangul-t3d-input-method
 "탁3D "
 "Hangul Tark Sebulshik D Input Method"
 "Input method: korean-hangul-t3d (mode line indicator:탁3D)\n\nHangul Tark Sebulshik D input method.")


(provide 'hangul-t3d)

;;; hangul-t3d.el ends here
