(* ** AES-NI *)
(* From eclib/AES.ec *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ word.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ssrnat.

Local Open Scope Z_scope.

Require Import ZArith.

Local Notation U8 i := (@mkWord 8 i erefl).

Definition Sbox (v1 : 8.-word) : 8.-word :=
  match toword v1 with
  | 0 => U8 99    | 1 => U8 124   | 2 => U8 119   | 3 => U8 123   | 4 => U8 242
  | 5 => U8 107   | 6 => U8 111   | 7 => U8 197   | 8 => U8 48    | 9 => U8 1
  | 10 => U8 103  | 11 => U8 43   | 12 => U8 254  | 13 => U8 215  | 14 => U8 171
  | 15 => U8 118  | 16 => U8 202  | 17 => U8 130  | 18 => U8 201  | 19 => U8 125
  | 20 => U8 250  | 21 => U8 89   | 22 => U8 71   | 23 => U8 240  | 24 => U8 173
  | 25 => U8 212  | 26 => U8 162  | 27 => U8 175  | 28 => U8 156  | 29 => U8 164
  | 30 => U8 114  | 31 => U8 192  | 32 => U8 183  | 33 => U8 253  | 34 => U8 147
  | 35 => U8 38   | 36 => U8 54   | 37 => U8 63   | 38 => U8 247  | 39 => U8 204
  | 40 => U8 52   | 41 => U8 165  | 42 => U8 229  | 43 => U8 241  | 44 => U8 113
  | 45 => U8 216  | 46 => U8 49   | 47 => U8 21   | 48 => U8 4    | 49 => U8 199
  | 50 => U8 35   | 51 => U8 195  | 52 => U8 24   | 53 => U8 150  | 54 => U8 5
  | 55 => U8 154  | 56 => U8 7    | 57 => U8 18   | 58 => U8 128  | 59 => U8 226
  | 60 => U8 235  | 61 => U8 39   | 62 => U8 178  | 63 => U8 117  | 64 => U8 9
  | 65 => U8 131  | 66 => U8 44   | 67 => U8 26   | 68 => U8 27   | 69 => U8 110
  | 70 => U8 90   | 71 => U8 160  | 72 => U8 82   | 73 => U8 59   | 74 => U8 214
  | 75 => U8 179  | 76 => U8 41   | 77 => U8 227  | 78 => U8 47   | 79 => U8 132
  | 80 => U8 83   | 81 => U8 209  | 82 => U8 0    | 83 => U8 237  | 84 => U8 32
  | 85 => U8 252  | 86 => U8 177  | 87 => U8 91   | 88 => U8 106  | 89 => U8 203
  | 90 => U8 190  | 91 => U8 57   | 92 => U8 74   | 93 => U8 76   | 94 => U8 88
  | 95 => U8 207  | 96 => U8 208  | 97 => U8 239  | 98 => U8 170  | 99 => U8 251
  | 100 => U8 67  | 101 => U8 77  | 102 => U8 51  | 103 => U8 133 | 104 => U8 69
  | 105 => U8 249 | 106 => U8 2   | 107 => U8 127 | 108 => U8 80  | 109 => U8 60
  | 110 => U8 159 | 111 => U8 168 | 112 => U8 81  | 113 => U8 163 | 114 => U8 64
  | 115 => U8 143 | 116 => U8 146 | 117 => U8 157 | 118 => U8 56  | 119 => U8 245
  | 120 => U8 188 | 121 => U8 182 | 122 => U8 218 | 123 => U8 33  | 124 => U8 16
  | 125 => U8 255 | 126 => U8 243 | 127 => U8 210 | 128 => U8 205 | 129 => U8 12
  | 130 => U8 19  | 131 => U8 236 | 132 => U8 95  | 133 => U8 151 | 134 => U8 68
  | 135 => U8 23  | 136 => U8 196 | 137 => U8 167 | 138 => U8 126 | 139 => U8 61
  | 140 => U8 100 | 141 => U8 93  | 142 => U8 25  | 143 => U8 115 | 144 => U8 96
  | 145 => U8 129 | 146 => U8 79  | 147 => U8 220 | 148 => U8 34  | 149 => U8 42
  | 150 => U8 144 | 151 => U8 136 | 152 => U8 70  | 153 => U8 238 | 154 => U8 184
  | 155 => U8 20  | 156 => U8 222 | 157 => U8 94  | 158 => U8 11  | 159 => U8 219
  | 160 => U8 224 | 161 => U8 50  | 162 => U8 58  | 163 => U8 10  | 164 => U8 73
  | 165 => U8 6   | 166 => U8 36  | 167 => U8 92  | 168 => U8 194 | 169 => U8 211
  | 170 => U8 172 | 171 => U8 98  | 172 => U8 145 | 173 => U8 149 | 174 => U8 228
  | 175 => U8 121 | 176 => U8 231 | 177 => U8 200 | 178 => U8 55  | 179 => U8 109
  | 180 => U8 141 | 181 => U8 213 | 182 => U8 78  | 183 => U8 169 | 184 => U8 108
  | 185 => U8 86  | 186 => U8 244 | 187 => U8 234 | 188 => U8 101 | 189 => U8 122
  | 190 => U8 174 | 191 => U8 8   | 192 => U8 186 | 193 => U8 120 | 194 => U8 37
  | 195 => U8 46  | 196 => U8 28  | 197 => U8 166 | 198 => U8 180 | 199 => U8 198
  | 200 => U8 232 | 201 => U8 221 | 202 => U8 116 | 203 => U8 31  | 204 => U8 75
  | 205 => U8 189 | 206 => U8 139 | 207 => U8 138 | 208 => U8 112 | 209 => U8 62
  | 210 => U8 181 | 211 => U8 102 | 212 => U8 72  | 213 => U8 3   | 214 => U8 246
  | 215 => U8 14  | 216 => U8 97  | 217 => U8 53  | 218 => U8 87  | 219 => U8 185
  | 220 => U8 134 | 221 => U8 193 | 222 => U8 29  | 223 => U8 158 | 224 => U8 225
  | 225 => U8 248 | 226 => U8 152 | 227 => U8 17  | 228 => U8 105 | 229 => U8 217
  | 230 => U8 142 | 231 => U8 148 | 232 => U8 155 | 233 => U8 30  | 234 => U8 135
  | 235 => U8 233 | 236 => U8 206 | 237 => U8 85  | 238 => U8 40  | 239 => U8 223
  | 240 => U8 140 | 241 => U8 161 | 242 => U8 137 | 243 => U8 13  | 244 => U8 191
  | 245 => U8 230 | 246 => U8 66  | 247 => U8 104 | 248 => U8 65  | 249 => U8 153
  | 250 => U8 45  | 251 => U8 15  | 252 => U8 176 | 253 => U8 84  | 254 => U8 187
  | 255 => U8 22  | _ => U8 0
  end.

Definition InvSbox (v1 : 8.-word) : 8.-word :=
  match toword v1 with
  | 0 => U8 82    | 1 => U8 9     | 2 => U8 106   | 3 => U8 213   | 4 => U8 48
  | 5 => U8 54    | 6 => U8 165   | 7 => U8 56    | 8 => U8 191   | 9 => U8 64
  | 10 => U8 163  | 11 => U8 158  | 12 => U8 129  | 13 => U8 243  | 14 => U8 215
  | 15 => U8 251  | 16 => U8 124  | 17 => U8 227  | 18 => U8 57   | 19 => U8 130
  | 20 => U8 155  | 21 => U8 47   | 22 => U8 255  | 23 => U8 135  | 24 => U8 52
  | 25 => U8 142  | 26 => U8 67   | 27 => U8 68   | 28 => U8 196  | 29 => U8 222
  | 30 => U8 233  | 31 => U8 203  | 32 => U8 84   | 33 => U8 123  | 34 => U8 148
  | 35 => U8 50   | 36 => U8 166  | 37 => U8 194  | 38 => U8 35   | 39 => U8 61
  | 40 => U8 238  | 41 => U8 76   | 42 => U8 149  | 43 => U8 11   | 44 => U8 66
  | 45 => U8 250  | 46 => U8 195  | 47 => U8 78   | 48 => U8 8    | 49 => U8 46
  | 50 => U8 161  | 51 => U8 102  | 52 => U8 40   | 53 => U8 217  | 54 => U8 36
  | 55 => U8 178  | 56 => U8 118  | 57 => U8 91   | 58 => U8 162  | 59 => U8 73
  | 60 => U8 109  | 61 => U8 139  | 62 => U8 209  | 63 => U8 37   | 64 => U8 114
  | 65 => U8 248  | 66 => U8 246  | 67 => U8 100  | 68 => U8 134  | 69 => U8 104
  | 70 => U8 152  | 71 => U8 22   | 72 => U8 212  | 73 => U8 164  | 74 => U8 92
  | 75 => U8 204  | 76 => U8 93   | 77 => U8 101  | 78 => U8 182  | 79 => U8 146
  | 80 => U8 108  | 81 => U8 112  | 82 => U8 72   | 83 => U8 80   | 84 => U8 253
  | 85 => U8 237  | 86 => U8 185  | 87 => U8 218  | 88 => U8 94   | 89 => U8 21
  | 90 => U8 70   | 91 => U8 87   | 92 => U8 167  | 93 => U8 141  | 94 => U8 157
  | 95 => U8 132  | 96 => U8 144  | 97 => U8 216  | 98 => U8 171  | 99 => U8 0
  | 100 => U8 140 | 101 => U8 188 | 102 => U8 211 | 103 => U8 10  | 104 => U8 247
  | 105 => U8 228 | 106 => U8 88  | 107 => U8 5   | 108 => U8 184 | 109 => U8 179
  | 110 => U8 69  | 111 => U8 6   | 112 => U8 208 | 113 => U8 44  | 114 => U8 30
  | 115 => U8 143 | 116 => U8 202 | 117 => U8 63  | 118 => U8 15  | 119 => U8 2
  | 120 => U8 193 | 121 => U8 175 | 122 => U8 189 | 123 => U8 3   | 124 => U8 1
  | 125 => U8 19  | 126 => U8 138 | 127 => U8 107 | 128 => U8 58  | 129 => U8 145
  | 130 => U8 17  | 131 => U8 65  | 132 => U8 79  | 133 => U8 103 | 134 => U8 220
  | 135 => U8 234 | 136 => U8 151 | 137 => U8 242 | 138 => U8 207 | 139 => U8 206
  | 140 => U8 240 | 141 => U8 180 | 142 => U8 230 | 143 => U8 115 | 144 => U8 150
  | 145 => U8 172 | 146 => U8 116 | 147 => U8 34  | 148 => U8 231 | 149 => U8 173
  | 150 => U8 53  | 151 => U8 133 | 152 => U8 226 | 153 => U8 249 | 154 => U8 55
  | 155 => U8 232 | 156 => U8 28  | 157 => U8 117 | 158 => U8 223 | 159 => U8 110
  | 160 => U8 71  | 161 => U8 241 | 162 => U8 26  | 163 => U8 113 | 164 => U8 29
  | 165 => U8 41  | 166 => U8 197 | 167 => U8 137 | 168 => U8 111 | 169 => U8 183
  | 170 => U8 98  | 171 => U8 14  | 172 => U8 170 | 173 => U8 24  | 174 => U8 190
  | 175 => U8 27  | 176 => U8 252 | 177 => U8 86  | 178 => U8 62  | 179 => U8 75
  | 180 => U8 198 | 181 => U8 210 | 182 => U8 121 | 183 => U8 32  | 184 => U8 154
  | 185 => U8 219 | 186 => U8 192 | 187 => U8 254 | 188 => U8 120 | 189 => U8 205
  | 190 => U8 90  | 191 => U8 244 | 192 => U8 31  | 193 => U8 221 | 194 => U8 168
  | 195 => U8 51  | 196 => U8 136 | 197 => U8 7   | 198 => U8 199 | 199 => U8 49
  | 200 => U8 177 | 201 => U8 18  | 202 => U8 16  | 203 => U8 89  | 204 => U8 39
  | 205 => U8 128 | 206 => U8 236 | 207 => U8 95  | 208 => U8 96  | 209 => U8 81
  | 210 => U8 127 | 211 => U8 169 | 212 => U8 25  | 213 => U8 181 | 214 => U8 74
  | 215 => U8 13  | 216 => U8 45  | 217 => U8 229 | 218 => U8 122 | 219 => U8 159
  | 220 => U8 147 | 221 => U8 201 | 222 => U8 156 | 223 => U8 239 | 224 => U8 160
  | 225 => U8 224 | 226 => U8 59  | 227 => U8 77  | 228 => U8 174 | 229 => U8 42
  | 230 => U8 245 | 231 => U8 176 | 232 => U8 200 | 233 => U8 235 | 234 => U8 187
  | 235 => U8 60  | 236 => U8 131 | 237 => U8 83  | 238 => U8 153 | 239 => U8 97
  | 240 => U8 23  | 241 => U8 43  | 242 => U8 4   | 243 => U8 126 | 244 => U8 186
  | 245 => U8 119 | 246 => U8 214 | 247 => U8 38  | 248 => U8 225 | 249 => U8 105
  | 250 => U8 20  | 251 => U8 99  | 252 => U8 85  | 253 => U8 33  | 254 => U8 12
  | 255 => U8 125 | _ => U8 0
  end.

(* NOTE: SubWord clashes with subword *)

Definition SubWord (v1 : (8 * 4).-word) : 32.-word :=
  wcat [tuple of [seq Sbox i | i <- wsplitn v1]].
Definition InvSubWord (v1 : (8 * 4).-word) : 32.-word :=
  wcat [tuple of [seq InvSbox i | i <- wsplitn v1]].
Definition RotWord (v1 : (8 * 4).-word) : 32.-word :=
  wcat [tuple (subword 1 8 v1); subword 2 8 v1; subword 3 8 v1; subword 0 8 v1].

Definition to_matrix (s : 128.-word) :=
  let s_ := fun i j => (subword (i * 8) 8 (subword (j * 32) 32 s)) in
  (s_ 0 0, s_ 0 1, s_ 0 2, s_ 0 3,
    s_ 1 0, s_ 1 1, s_ 1 2, s_ 1 3,
    s_ 2 0, s_ 2 1, s_ 2 2, s_ 2 2,
    s_ 3 0, s_ 3 1, s_ 3 2, s_ 3 3)%nat.

Definition to_state (m : 8.-word * 8.-word * 8.-word * 8.-word *
                           8.-word * 8.-word * 8.-word * 8.-word *
                           8.-word * 8.-word * 8.-word * 8.-word *
                           8.-word * 8.-word * 8.-word * 8.-word)  :=
  let '(s00, s01, s02, s03,
        s10, s11, s12, s13,
        s20, s21, s22, s23,
        s30, s31, s32, s33) := m in
  let c0 := wcat [tuple s00; s10; s20; s30] in
  let c1 := wcat [tuple s01; s11; s21; s31] in
  let c2 := wcat [tuple s02; s12; s22; s32] in
  let c3 := wcat [tuple s03; s13; s23; s33] in
  wcat [tuple c0; c1; c2; c3].

Definition SubBytes (s : (32 * 4).-word) : 128.-word :=
  wcat [tuple of [seq SubWord i | i <- wsplitn s]].
Definition InvSubBytes (s : (32 * 4).-word) : 128.-word :=
  wcat [tuple of [seq InvSubWord i | i <- wsplitn s]].

Definition ShiftRows (s : 128.-word) :=
 let '(s00, s01, s02, s03,
       s10, s11, s12, s13,
       s20, s21, s22, s23,
       s30, s31, s32, s33) := to_matrix s in
 to_state (s00, s01, s02, s03,
           s11, s12, s13, s10,
           s22, s23, s20, s21,
           s33, s30, s31, s32).

Definition InvShiftRows (s : 128.-word) :=
 let '(s00, s01, s02, s03,
       s11, s12, s13, s10,
       s22, s23, s20, s21,
       s33, s30, s31, s32) := to_matrix s in
 to_state
    (s00, s01, s02, s03,
     s10, s11, s12, s13,
     s20, s21, s22, s23,
     s30, s31, s32, s33).

(* TODO: Implement these *)
Parameter MixColumns : 128.-word -> 128.-word.
Parameter InvMixColumns : 128.-word -> 128.-word.

Definition wAESDEC (state rkey : 128.-word) : 128.-word :=
  let state := InvShiftRows state in
  let state := InvSubBytes state in
  let state := InvMixColumns state in
  wxor state rkey.

Definition wAESDECLAST (state rkey : 128.-word) : 128.-word :=
  let state := InvShiftRows state in
  let state := InvSubBytes state in
  wxor state rkey.

Definition wAESENC (state rkey : 128.-word) : 128.-word :=
  let state := ShiftRows state in
  let state := SubBytes state in
  let state := MixColumns state in
  wxor state rkey.

Definition wAESENCLAST (state rkey : 128.-word) : 128.-word :=
  let state := ShiftRows state in
  let state := SubBytes state in
  wxor state rkey.

Notation wAESIMC := InvMixColumns.

Definition wAESKEYGENASSIST (v1 : 128.-word) (v2 : 8.-word) : 128.-word :=
  let rcon := subword 0 32 v2 in
  let x1 := subword (1 * 32) 32 v1 in
  let x3 := subword (3 * 32) 32 v1 in
  let y0 := SubWord x1 in
  let y1 := wxor (RotWord (SubWord x1)) rcon in
  let y2 := SubWord x3 in
  let y3 := wxor (RotWord (SubWord x3)) rcon in
  wcat [tuple y0; y1; y2; y3].

Definition wAESENC_ (state rkey : 128.-word) : 128.-word :=
  let state := SubBytes state in
  let state := ShiftRows state in
  let state := MixColumns state in
  wxor state rkey.

Definition wAESENCLAST_ (state rkey : 128.-word) : 128.-word :=
  let state := SubBytes state in
  let state := ShiftRows state in
  wxor state rkey.

Definition wAESDEC_ (state rkey: 128.-word) : 128.-word :=
  let state := InvShiftRows state in
  let state := InvSubBytes state in
  let state := wxor state rkey in
  InvMixColumns state.
