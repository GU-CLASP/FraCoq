module AnswerTypes where

data Answer = Yes | No | Unknown | Undef | Unclear String deriving (Eq,Show,Ord)

answers = 
   [ ( 1 , Yes )
   , ( 2 , Yes )
   , ( 3 , Yes )
   , ( 4 , Yes )
   , ( 5 , Yes )
   , ( 6 , No )
   , ( 7 , Yes )
   , ( 8 , Yes )
   , ( 9 , Yes )
   , ( 10 , Yes )
   , ( 11 , Yes )
   , ( 12 , Unclear "Not many" )
   , ( 13 , Yes )
   , ( 14 , No )
   , ( 15 , Yes )
   , ( 16 , Unclear "At most two" )
   , ( 17 , Yes )
   , ( 18 , Yes )
   , ( 19 , Yes )
   , ( 20 , Yes )
   , ( 21 , Yes )
   , ( 22 , Unknown )
   , ( 23 , Yes )
   , ( 24 , Yes )
   , ( 25 , Yes )
   , ( 26 , Yes )
   , ( 27 , Yes )
   , ( 28 , Unknown )
   , ( 29 , Yes )
   , ( 30 , Unknown )
   , ( 31 , Yes )
   , ( 32 , Unknown )
   , ( 33 , Unknown )
   , ( 34 , Unknown )
   , ( 35 , Unknown )
   , ( 36 , Unknown )
   , ( 37 , Unknown )
   , ( 38 , No )
   , ( 39 , Unknown )
   , ( 40 , Unknown )
   , ( 41 , Unknown )
   , ( 42 , Unknown )
   , ( 43 , Unknown )
   , ( 44 , Yes )
   , ( 45 , Unknown )
   , ( 46 , No )
   , ( 47 , Unknown )
   , ( 48 , Yes )
   , ( 49 , Yes )
   , ( 50 , Unknown )
   , ( 51 , Unknown )
   , ( 52 , Unknown )
   , ( 53 , Unknown )
   , ( 54 , Unknown )
   , ( 55 , Yes )
   , ( 56 , Unknown )
   , ( 57 , Yes )
   , ( 58 , Unknown )
   , ( 59 , Yes )
   , ( 60 , Unknown )
   , ( 61
     , Unclear
         "Yes, if both commissioners are female; otherwise there are more than two commissioners."
     )
   , ( 62
     , Unclear
         "No, if both commissioners are female; otherwise there are more than two commissioners."
     )
   , ( 63 , Yes )
   , ( 64 , Unknown )
   , ( 65 , Unknown )
   , ( 66 , Yes )
   , ( 67 , Yes )
   , ( 68 , Yes )
   , ( 69 , Yes )
   , ( 70 , No )
   , ( 71 , Unknown )
   , ( 72 , Unknown )
   , ( 73 , Unknown )
   , ( 74 , Unknown )
   , ( 75 , Unknown )
   , ( 76 , Yes )
   , ( 77
     , Unclear
         "Yes, if both commissioners are female; otherwise there are more than two commissioners."
     )
   , ( 78
     , Unclear
         "No, if both commissioners are female; otherwise there are more than two commissioners."
     )
   , ( 79 , Unknown )
   , ( 80 , Yes )
   , ( 81 , Yes )
   , ( 82 , Yes )
   , ( 83 , Unknown )
   , ( 84 , Yes )
   , ( 85 , No )
   , ( 86 , No )
   , ( 87 , Unclear "Yes, on one reading" )
   , ( 88 , Unclear "Don't know, on one reading" )
   , ( 89 , Yes )
   , ( 90 , Yes )
   , ( 91 , Unknown )
   , ( 92 , Yes )
   , ( 93 , Yes )
   , ( 94 , Unknown )
   , ( 95 , Unknown )
   , ( 96 , Yes )
   , ( 97 , Yes )
   , ( 98 , Unknown )
   , ( 99 , Yes )
   , ( 100 , Yes )
   , ( 101 , Yes )
   , ( 102 , Unknown )
   , ( 103 , Yes )
   , ( 104 , Unknown )
   , ( 105 , No )
   , ( 106 , No )
   , ( 107 , Yes )
   , ( 108 , Yes )
   , ( 109 , Unclear "No, just one" )
   , ( 110 , Yes )
   , ( 111
     , Unclear
         "Yes, on a collective/cumulative reading of the conclusion."
     )
   , ( 112
     , Unclear "Yes, on a distributive reading of \"Smith and Jones\"."
     )
   , ( 113 , Yes )
   , ( 114 , Yes )
   , ( 115 , Yes )
   , ( 116 , Yes )
   , ( 117 , Yes )
   , ( 118 , Yes )
   , ( 119 , No )
   , ( 120 , Yes )
   , ( 121 , Yes )
   , ( 122 , Yes )
   , ( 123 , Yes )
   , ( 124 , Yes )
   , ( 125 , Unknown )
   , ( 126 , Yes )
   , ( 127
     , Unclear "Yes, on a distributive reading of the question."
     )
   , ( 128 , Yes )
   , ( 129 , Unclear "Yes, on one possible reading" )
   , ( 130 , Unclear "Don't know, on one possible reading" )
   , ( 131 , Yes )
   , ( 132 , Yes )
   , ( 133 , Yes )
   , ( 134 , Yes )
   , ( 135 , Yes )
   , ( 136 , Unknown )
   , ( 137 , Yes )
   , ( 138 , Yes )
   , ( 139 , Yes )
   , ( 140 , Yes )
   , ( 141 , Unknown )
   , ( 142 , Yes )
   , ( 143 , Unknown )
   , ( 144 , Yes )
   , ( 145 , Yes )
   , ( 146 , Yes )
   , ( 147 , No )
   , ( 148 , Yes )
   , ( 149 , Yes )
   , ( 150 , Yes )
   , ( 151 , Yes )
   , ( 152 , Yes )
   , ( 153 , Yes )
   , ( 154 , Yes )
   , ( 155 , Yes )
   , ( 156 , Unknown )
   , ( 157 , Yes )
   , ( 158 , Unknown )
   , ( 159 , Yes )
   , ( 160 , Unclear "Yes, on one possible reading" )
   , ( 161 , Unclear "Don't know, on one possible reading" )
   , ( 162 , Yes )
   , ( 163 , No )
   , ( 164 , Yes )
   , ( 165 , Yes )
   , ( 166 , Yes )
   , ( 167 , No )
   , ( 168 , Yes )
   , ( 169 , Unclear "Yes, on one possible reading" )
   , ( 170 , Unclear "Yes, on one possible reading" )
   , ( 171 , Yes )
   , ( 172 , Yes )
   , ( 173 , Yes )
   , ( 174 , Unknown )
   , ( 175 , Unclear "Yes, on one possible reading/parse" )
   , ( 176 , Unclear "Yes, on one possible reading/parse" )
   , ( 177 , Unknown )
   , ( 178 , Yes )
   , ( 179 , Yes )
   , ( 180 , Yes )
   , ( 181 , Unknown )
   , ( 182 , Unclear "Yes, on one reading" )
   , ( 183 , Unclear "Yes, on one reading" )
   , ( 184 , Unknown )
   , ( 185 , Unclear "Yes, on one reading" )
   , ( 186 , Unclear "Yes, on one reading" )
   , ( 187 , Unclear "Yes, on one reading" )
   , ( 188 , Unknown )
   , ( 189 , Unclear "Yes, on one reading" )
   , ( 190 , Unclear "Yes, on one reading" )
   , ( 191 , Yes )
   , ( 192 , Unknown )
   , ( 193 , Yes )
   , ( 194 , Unknown )
   , ( 195 , Yes )
   , ( 196 , Yes )
   , ( 197 , Yes )
   , ( 198 , Unclear "No / don't know" )
   , ( 199 , Unclear "Yes (for a former university student)" )
   , ( 200 , Unknown )
   , ( 201 , Unknown )
   , ( 202 , Yes )
   , ( 203 , Yes )
   , ( 204 , No )
   , ( 205 , No )
   , ( 206 , Unknown )
   , ( 207 , Unknown )
   , ( 208 , Yes )
   , ( 209 , No )
   , ( 210 , No )
   , ( 211 , No )
   , ( 212 , Yes )
   , ( 213 , Unclear "??: Yes for a mouse; ?? No for an animal" )
   , ( 214 , Yes )
   , ( 215 , Unknown )
   , ( 216 , Yes )
   , ( 217 , Unknown )
   , ( 218 , Yes )
   , ( 219 , Unknown )
   , ( 220 , Yes )
   , ( 221 , Unknown )
   , ( 222 , Unknown )
   , ( 223 , No )
   , ( 224 , Yes )
   , ( 225 , Unknown )
   , ( 226 , Unknown )
   , ( 227 , No )
   , ( 228 , Unknown )
   , ( 229 , No )
   , ( 230 , Yes )
   , ( 231 , Unknown )
   , ( 232 , Yes )
   , ( 233 , Yes )
   , ( 234 , Unknown )
   , ( 235 , Yes )
   , ( 236 , Yes )
   , ( 237 , Yes )
   , ( 238 , Yes )
   , ( 239 , Yes )
   , ( 240 , Unknown )
   , ( 241 , Yes )
   , ( 242 , Yes )
   , ( 243 , Yes )
   , ( 244 , Unclear "Yes, on one reading of the premise" )
   , ( 245 , Unclear "Yes, on one reading of the premise" )
   , ( 246 , Yes )
   , ( 247 , Unknown )
   , ( 248 , Yes )
   , ( 249 , Yes )
   , ( 250 , Unclear "Yes, on one reading of the premise" )
   , ( 251 , Yes )
   , ( 252 , Yes )
   , ( 253 , Unknown )
   , ( 254 , Unknown )
   , ( 255 , Yes )
   , ( 256 , Unclear "Don't know, on one reading of the premise" )
   , ( 257 , Unclear "Yes, on one reading of the premise" )
   , ( 258 , No )
   , ( 259 , Yes )
   , ( 260 , Yes )
   , ( 261 , Yes )
   , ( 262 , Yes )
   , ( 263 , Unknown )
   , ( 264 , Yes )
   , ( 265 , Yes )
   , ( 266 , Yes )
   , ( 267 , Yes )
   , ( 268 , Yes )
   , ( 269 , Unknown )
   , ( 270 , Yes )
   , ( 271 , Unknown )
   , ( 272 , Unknown )
   , ( 273 , Unknown )
   , ( 274 , Unknown )
   , ( 275 , Unknown )
   , ( 276 , Unclear "" )
   , ( 277 , Unknown )
   , ( 278 , No )
   , ( 279 , No )
   , ( 280 , Unknown )
   , ( 281 , Unknown )
   , ( 282 , No )
   , ( 283 , Unknown )
   , ( 284 , Yes )
   , ( 285 , Unknown )
   , ( 286 , No )
   , ( 287 , Unknown )
   , ( 288 , Yes )
   , ( 289 , No )
   , ( 290 , Yes )
   , ( 291 , Unclear "?Yes" )
   , ( 292 , Unknown )
   , ( 293 , Unknown )
   , ( 294 , Yes )
   , ( 295 , Unknown )
   , ( 296 , Unknown )
   , ( 297 , Yes )
   , ( 298 , Yes )
   , ( 299 , No )
   , ( 300 , Yes )
   , ( 301 , Yes )
   , ( 302 , Yes )
   , ( 303 , Yes )
   , ( 304 , Unknown )
   , ( 305 , Unclear "" )
   , ( 306 , Yes )
   , ( 307 , Yes )
   , ( 308
     , Unclear "Yes on one scoping; unknown on another scoping"
     )
   , ( 309 , Unclear "" )
   , ( 310 , Unclear "" )
   , ( 311 , Yes )
   , ( 312 , Yes )
   , ( 313 , No )
   , ( 314 , Yes )
   , ( 315 , Yes )
   , ( 316 , Yes )
   , ( 317 , Yes )
   , ( 318 , No )
   , ( 319 , Yes )
   , ( 320 , Yes )
   , ( 321 , Yes )
   , ( 322 , Yes )
   , ( 323 , Yes )
   , ( 324 , Yes )
   , ( 325 , Yes )
   , ( 326 , Yes )
   , ( 327 , Unknown )
   , ( 328 , Yes )
   , ( 329 , Unknown )
   , ( 330 , Yes )
   , ( 331 , Yes )
   , ( 332 , Yes )
   , ( 333 , Yes )
   , ( 334 , Yes )
   , ( 335 , Unknown )
   , ( 336 , Yes )
   , ( 337 , Unknown )
   , ( 338 , Yes )
   , ( 339 , No )
   , ( 340 , Unknown )
   , ( 341 , Unknown )
   , ( 342 , Yes )
   , ( 343 , Yes )
   , ( 344 , Yes )
   , ( 345 , Yes )
   , ( 346 , Yes )
   ]


