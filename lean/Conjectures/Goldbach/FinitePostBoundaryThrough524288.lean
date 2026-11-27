import Mathlib

/-!
# Prime pairs in the block immediately above offset 262144

The 57 original offsets and the translation-closure argument come from
PR #3706, commit 25cc1158ef5f053ed8e0a0ca1a4f69820fbd6c4b. The eleven
additional offsets are the F01 repair set in the project's fourth task plan.
Each large summand has a recursive Lucas certificate. The sieve excludes
multiples of every prime up to 877 and checks the whole translated interval.
-/

namespace PostBoundary524288.Anchors

set_option maxHeartbeats 2000000

private theorem prime_2847 : Nat.Prime 3999999999999997153 := by
  primality (cert := .witnesses [
    .lucas { root := 7, primeFactors := [2, 3, 17, 61, 5393, 15329, 162011] },
    .lucas { root := 3, primeFactors := [2, 337] },
    .lucas { root := 3, primeFactors := [2, 479] },
    .lucas { root := 2, primeFactors := [2, 5, 17, 953] }])

private theorem prime_10403 : Nat.Prime 3999999999999989597 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 13, 4091, 6317, 18803, 158303] },
    .lucas { root := 2, primeFactors := [2, 5, 409] },
    .lucas { root := 2, primeFactors := [2, 1579] },
    .lucas { root := 3, primeFactors := [2, 3, 263] },
    .lucas { root := 5, primeFactors := [2, 7, 17, 79] },
    .lucas { root := 5, primeFactors := [2, 79151] },
    .lucas { root := 13, primeFactors := [2, 5, 1583] },
    .lucas { root := 5, primeFactors := [2, 7, 113] }])

private theorem prime_8949 : Nat.Prime 3999999999999991051 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 5, 7, 79, 751, 13789, 1552207] },
    .lucas { root := 7, primeFactors := [2, 3, 383] },
    .lucas { root := 3, primeFactors := [2, 3, 61, 4241] },
    .lucas { root := 3, primeFactors := [2, 5, 53] }])

private theorem prime_57071 : Nat.Prime 3999999999999942929 := by
  primality (cert := .witnesses [
    .lucas { root := 6, primeFactors := [2, 11, 31, 449, 1427, 3803, 300877] },
    .lucas { root := 2, primeFactors := [2, 23, 31] },
    .lucas { root := 2, primeFactors := [2, 1901] },
    .lucas { root := 2, primeFactors := [2, 5, 19] },
    .lucas { root := 2, primeFactors := [2, 3, 25073] },
    .lucas { root := 3, primeFactors := [2, 1567] },
    .lucas { root := 3, primeFactors := [2, 3, 29] }])

private theorem prime_15077 : Nat.Prime 3999999999999984923 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 23, 2579, 13127, 17443, 147253] },
    .lucas { root := 2, primeFactors := [2, 1289] },
    .lucas { root := 6, primeFactors := [2, 7, 23] },
    .lucas { root := 5, primeFactors := [2, 6563] },
    .lucas { root := 5, primeFactors := [2, 17, 193] },
    .lucas { root := 2, primeFactors := [2, 3, 17, 19] },
    .lucas { root := 2, primeFactors := [2, 3, 7, 1753] },
    .lucas { root := 7, primeFactors := [2, 3, 73] }])

private theorem prime_24621 : Nat.Prime 3999999999999975379 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 3, 11, 727, 4159, 5333, 341687] },
    .lucas { root := 3, primeFactors := [2, 3, 7, 11] },
    .lucas { root := 2, primeFactors := [2, 31, 43] },
    .lucas { root := 5, primeFactors := [2, 170843] },
    .lucas { root := 2, primeFactors := [2, 7, 12203] },
    .lucas { root := 2, primeFactors := [2, 6101] },
    .lucas { root := 2, primeFactors := [2, 5, 61] }])

private theorem prime_7199 : Nat.Prime 3999999999999992801 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 5, 7, 17, 2153, 10529, 1853497] },
    .lucas { root := 3, primeFactors := [2, 269] },
    .lucas { root := 3, primeFactors := [2, 7, 47] },
    .lucas { root := 5, primeFactors := [2, 3, 8581] },
    .lucas { root := 6, primeFactors := [2, 3, 5, 11, 13] }])

private theorem prime_13923 : Nat.Prime 3999999999999986077 := by
  primality (cert := .witnesses [
    .lucas { root := 5, primeFactors := [2, 3, 47, 113, 149, 1459, 4861, 59393] },
    .lucas { root := 3, primeFactors := [2, 3] },
    .lucas { root := 11, primeFactors := [2, 3, 5] },
    .lucas { root := 5, primeFactors := [2, 29] }])

private theorem prime_18117 : Nat.Prime 3999999999999981883 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 3, 2557, 6421, 8501, 4776451] },
    .lucas { root := 2, primeFactors := [2, 3, 71] },
    .lucas { root := 6, primeFactors := [2, 3, 5, 107] },
    .lucas { root := 7, primeFactors := [2, 5, 17] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 7, 4549] },
    .lucas { root := 6, primeFactors := [2, 3, 379] }])

private theorem prime_67583 : Nat.Prime 3999999999999932417 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 17, 53, 773, 1723, 1627573] },
    .lucas { root := 3, primeFactors := [2, 3, 7, 41] },
    .lucas { root := 5, primeFactors := [2, 3, 23, 5897] },
    .lucas { root := 3, primeFactors := [2, 11, 67] }])

private theorem prime_59751 : Nat.Prime 3999999999999940249 := by
  primality (cert := .witnesses [
    .lucas { root := 21, primeFactors := [2, 3, 13, 971, 1117, 6899, 1713353] },
    .lucas { root := 2, primeFactors := [2, 3, 31] },
    .lucas { root := 2, primeFactors := [2, 3449] },
    .lucas { root := 3, primeFactors := [2, 431] },
    .lucas { root := 3, primeFactors := [2, 79, 2711] },
    .lucas { root := 7, primeFactors := [2, 5, 271] }])

private theorem prime_68609 : Nat.Prime 3999999999999931391 := by
  primality (cert := .witnesses [
    .lucas { root := 14, primeFactors := [2, 5, 1907, 5849, 22367, 1603319] },
    .lucas { root := 2, primeFactors := [2, 953] },
    .lucas { root := 3, primeFactors := [2, 17, 43] },
    .lucas { root := 5, primeFactors := [2, 53, 211] },
    .lucas { root := 7, primeFactors := [2, 151, 5309] },
    .lucas { root := 2, primeFactors := [2, 1327] },
    .lucas { root := 3, primeFactors := [2, 3, 13, 17] }])

private theorem prime_88623 : Nat.Prime 3999999999999911377 := by
  primality (cert := .witnesses [
    .lucas { root := 15, primeFactors := [2, 3, 7, 41, 151, 8447, 9811, 23203] },
    .lucas { root := 5, primeFactors := [2, 41, 103] },
    .lucas { root := 3, primeFactors := [2, 3, 5, 109] },
    .lucas { root := 3, primeFactors := [2, 3, 1289] },
    .lucas { root := 6, primeFactors := [2, 7, 23] }])

private theorem prime_42857 : Nat.Prime 3999999999999957143 := by
  primality (cert := .witnesses [
    .lucas { root := 7, primeFactors := [2, 7, 163, 457, 691, 13451, 412663] },
    .lucas { root := 2, primeFactors := [2, 5, 269] },
    .lucas { root := 3, primeFactors := [2, 3, 68777] },
    .lucas { root := 3, primeFactors := [2, 8597] },
    .lucas { root := 2, primeFactors := [2, 7, 307] }])

private theorem prime_135221 : Nat.Prime 3999999999999864779 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 431, 593, 1217, 5531, 1162529] },
    .lucas { root := 3, primeFactors := [2, 19] },
    .lucas { root := 10, primeFactors := [2, 5, 7, 79] },
    .lucas { root := 3, primeFactors := [2, 17, 2137] },
    .lucas { root := 10, primeFactors := [2, 3, 89] }])

private theorem prime_36099 : Nat.Prime 3999999999999963901 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 3, 5, 17, 23, 127, 839, 1877, 170503] },
    .lucas { root := 2, primeFactors := [2, 7, 67] },
    .lucas { root := 5, primeFactors := [2, 3, 157, 181] }])

private theorem prime_77099 : Nat.Prime 3999999999999922901 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 5, 149, 1201, 3119, 5869, 12211] },
    .lucas { root := 11, primeFactors := [2, 3, 5] },
    .lucas { root := 7, primeFactors := [2, 1559] },
    .lucas { root := 19, primeFactors := [2, 19, 41] },
    .lucas { root := 2, primeFactors := [2, 3, 163] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 11, 37] }])

private theorem prime_137733 : Nat.Prime 3999999999999862267 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 31, 859, 4799, 16141, 323201] },
    .lucas { root := 7, primeFactors := [2, 2399] },
    .lucas { root := 11, primeFactors := [2, 11, 109] },
    .lucas { root := 6, primeFactors := [2, 3, 5, 269] },
    .lucas { root := 3, primeFactors := [2, 5, 101] }])

private theorem prime_72683 : Nat.Prime 3999999999999927317 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 17, 67, 113, 1607, 5153, 938257] },
    .lucas { root := 5, primeFactors := [2, 11, 73] },
    .lucas { root := 5, primeFactors := [2, 7, 23] },
    .lucas { root := 13, primeFactors := [2, 3, 11, 1777] },
    .lucas { root := 5, primeFactors := [2, 3, 37] }])

private theorem prime_180381 : Nat.Prime 3999999999999819619 := by
  primality (cert := .witnesses [
    .lucas { root := 10, primeFactors := [2, 3, 11, 41, 101, 997, 12149, 402767] },
    .lucas { root := 2, primeFactors := [2, 3037] },
    .lucas { root := 2, primeFactors := [2, 3, 11, 23] },
    .lucas { root := 5, primeFactors := [2, 7, 13, 2213] },
    .lucas { root := 2, primeFactors := [2, 7, 79] }])

private theorem prime_21647 : Nat.Prime 3999999999999978353 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 7, 1367, 16217, 4696873] },
    .lucas { root := 5, primeFactors := [2, 683] },
    .lucas { root := 3, primeFactors := [2, 2027] },
    .lucas { root := 2, primeFactors := [2, 1013] },
    .lucas { root := 5, primeFactors := [2, 3, 31, 59, 107] }])

private theorem prime_109899 : Nat.Prime 3999999999999890101 := by
  primality (cert := .witnesses [
    .lucas { root := 6, primeFactors := [2, 3, 5, 19, 73, 193, 23209, 2146093] },
    .lucas { root := 31, primeFactors := [2, 3, 967] },
    .lucas { root := 2, primeFactors := [2, 3, 13, 13757] },
    .lucas { root := 2, primeFactors := [2, 19, 181] }])

private theorem prime_130751 : Nat.Prime 3999999999999869249 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 29, 89, 1601, 8377, 1805561] },
    .lucas { root := 3, primeFactors := [2, 5] },
    .lucas { root := 5, primeFactors := [2, 3, 349] },
    .lucas { root := 3, primeFactors := [2, 5, 45139] },
    .lucas { root := 2, primeFactors := [2, 3, 7523] },
    .lucas { root := 2, primeFactors := [2, 3761] },
    .lucas { root := 3, primeFactors := [2, 5, 47] }])

private theorem prime_96417 : Nat.Prime 3999999999999903583 := by
  primality (cert := .witnesses [
    .lucas { root := 5, primeFactors := [2, 3, 181, 1667, 2111, 9479, 110419] },
    .lucas { root := 2, primeFactors := [2, 7, 17] },
    .lucas { root := 7, primeFactors := [2, 5, 211] },
    .lucas { root := 7, primeFactors := [2, 7, 677] },
    .lucas { root := 3, primeFactors := [2, 3, 7, 11, 239] }])

private theorem prime_154643 : Nat.Prime 3999999999999845357 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 43, 751, 2503, 3181, 3889261] },
    .lucas { root := 3, primeFactors := [2, 3, 139] },
    .lucas { root := 7, primeFactors := [2, 3, 5, 53] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 17, 31, 41] }])

private theorem prime_225219 : Nat.Prime 3999999999999774781 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 3, 5, 359, 2273, 5519, 4934387] },
    .lucas { root := 3, primeFactors := [2, 71] },
    .lucas { root := 13, primeFactors := [2, 31, 89] },
    .lucas { root := 2, primeFactors := [2, 17, 8537] },
    .lucas { root := 3, primeFactors := [2, 11, 97] }])

private theorem prime_175737 : Nat.Prime 3999999999999824263 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 13, 17, 149, 587, 20693, 42737] },
    .lucas { root := 2, primeFactors := [2, 7, 739] },
    .lucas { root := 3, primeFactors := [2, 2671] },
    .lucas { root := 7, primeFactors := [2, 3, 5, 89] }])

private theorem prime_214319 : Nat.Prime 3999999999999785681 := by
  primality (cert := .witnesses [
    .lucas { root := 6, primeFactors := [2, 5, 1289, 2707, 13421, 1067687] },
    .lucas { root := 6, primeFactors := [2, 7, 23] },
    .lucas { root := 2, primeFactors := [2, 3, 11, 41] },
    .lucas { root := 10, primeFactors := [2, 5, 11, 61] },
    .lucas { root := 5, primeFactors := [2, 19, 28097] },
    .lucas { root := 3, primeFactors := [2, 439] }])

private theorem prime_245771 : Nat.Prime 3999999999999754229 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 193, 1129, 2237, 13873, 147881] },
    .lucas { root := 11, primeFactors := [2, 3, 47] },
    .lucas { root := 2, primeFactors := [2, 13, 43] },
    .lucas { root := 5, primeFactors := [2, 3, 17] },
    .lucas { root := 3, primeFactors := [2, 5, 3697] },
    .lucas { root := 5, primeFactors := [2, 3, 7, 11] }])

private theorem prime_223701 : Nat.Prime 3999999999999776299 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 43, 67, 167, 523, 6581, 402583] },
    .lucas { root := 14, primeFactors := [2, 5, 7, 47] },
    .lucas { root := 3, primeFactors := [2, 3, 229, 293] }])

private theorem prime_197163 : Nat.Prime 3999999999999802837 := by
  primality (cert := .witnesses [
    .lucas { root := 5, primeFactors := [2, 3, 281, 617, 1163, 7499, 220447] },
    .lucas { root := 5, primeFactors := [2, 7, 83] },
    .lucas { root := 2, primeFactors := [2, 23, 163] },
    .lucas { root := 3, primeFactors := [2, 3, 37, 331] }])

private theorem prime_145967 : Nat.Prime 3999999999999854033 := by
  primality (cert := .witnesses [
    .lucas { root := 5, primeFactors := [2, 7, 13, 631, 2557, 9281, 183461] },
    .lucas { root := 2, primeFactors := [2, 3, 71] },
    .lucas { root := 3, primeFactors := [2, 5, 29] },
    .lucas { root := 7, primeFactors := [2, 5, 9173] },
    .lucas { root := 2, primeFactors := [2, 2293] },
    .lucas { root := 2, primeFactors := [2, 3, 191] }])

private theorem prime_203699 : Nat.Prime 3999999999999796301 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 5, 1811, 4363, 11399, 444109] },
    .lucas { root := 6, primeFactors := [2, 5, 181] },
    .lucas { root := 2, primeFactors := [2, 3, 727] },
    .lucas { root := 11, primeFactors := [2, 41, 139] },
    .lucas { root := 10, primeFactors := [2, 3, 7, 17, 311] }])

private theorem prime_191103 : Nat.Prime 3999999999999808897 := by
  primality (cert := .witnesses [
    .lucas { root := 17, primeFactors := [2, 3, 7, 13, 137, 1447, 3407, 169483] },
    .lucas { root := 3, primeFactors := [2, 3, 241] },
    .lucas { root := 5, primeFactors := [2, 13, 131] },
    .lucas { root := 3, primeFactors := [2, 3, 47, 601] }])

private theorem prime_113963 : Nat.Prime 3999999999999886037 := by
  primality (cert := .witnesses [
    .lucas { root := 19, primeFactors := [2, 7, 11, 37, 773, 21379, 3034189] },
    .lucas { root := 2, primeFactors := [2, 3, 7, 509] },
    .lucas { root := 2, primeFactors := [2, 3, 89, 947] }])

private theorem prime_90447 : Nat.Prime 3999999999999909553 := by
  primality (cert := .witnesses [
    .lucas { root := 5, primeFactors := [2, 3, 787, 2953, 24671, 1453429] },
    .lucas { root := 13, primeFactors := [2, 3, 41] },
    .lucas { root := 11, primeFactors := [2, 5, 2467] },
    .lucas { root := 2, primeFactors := [2, 3, 137] },
    .lucas { root := 2, primeFactors := [2, 3, 47, 859] }])

private theorem prime_132663 : Nat.Prime 3999999999999867337 := by
  primality (cert := .witnesses [
    .lucas { root := 14, primeFactors := [2, 3, 11, 71, 79, 97, 11981, 774791] },
    .lucas { root := 2, primeFactors := [2, 5, 599] },
    .lucas { root := 19, primeFactors := [2, 5, 77479] },
    .lucas { root := 6, primeFactors := [2, 3, 37, 349] }])

private theorem prime_39647 : Nat.Prime 3999999999999960353 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 11, 193, 401, 1699, 3449, 25057] },
    .lucas { root := 3, primeFactors := [2, 3, 283] },
    .lucas { root := 3, primeFactors := [2, 431] },
    .lucas { root := 5, primeFactors := [2, 3, 29] }])

private theorem prime_188079 : Nat.Prime 3999999999999811921 := by
  primality (cert := .witnesses [
    .lucas { root := 31, primeFactors := [2, 3, 5, 7, 17, 2687, 15773, 3304607] },
    .lucas { root := 5, primeFactors := [2, 17, 79] },
    .lucas { root := 2, primeFactors := [2, 3943] },
    .lucas { root := 3, primeFactors := [2, 3, 73] },
    .lucas { root := 5, primeFactors := [2, 131, 12613] },
    .lucas { root := 2, primeFactors := [2, 3, 1051] },
    .lucas { root := 7, primeFactors := [2, 3, 5, 7] }])

private theorem prime_204491 : Nat.Prime 3999999999999795509 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 487, 857, 1063, 4021, 560561] },
    .lucas { root := 3, primeFactors := [2, 3, 59] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 67] },
    .lucas { root := 17, primeFactors := [2, 5, 7, 11, 13] }])

private theorem prime_113129 : Nat.Prime 3999999999999886871 := by
  primality (cert := .witnesses [
    .lucas { root := 7, primeFactors := [2, 5, 13, 19, 89, 257, 1201, 4139, 14243] },
    .lucas { root := 11, primeFactors := [2, 3, 5] },
    .lucas { root := 2, primeFactors := [2, 2069] },
    .lucas { root := 2, primeFactors := [2, 11, 47] },
    .lucas { root := 2, primeFactors := [2, 7121] },
    .lucas { root := 3, primeFactors := [2, 5, 89] }])

private theorem prime_233241 : Nat.Prime 3999999999999766759 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 163, 173, 199, 233, 293, 1740197] },
    .lucas { root := 2, primeFactors := [2, 439, 991] }])

private theorem prime_13547 : Nat.Prime 3999999999999986453 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 31, 47, 97, 419, 8627, 1957469] },
    .lucas { root := 2, primeFactors := [2, 19, 227] },
    .lucas { root := 2, primeFactors := [2, 489367] },
    .lucas { root := 5, primeFactors := [2, 3, 31, 877] }])

private theorem prime_182783 : Nat.Prime 3999999999999817217 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 13, 19, 37, 5981, 3862921] },
    .lucas { root := 3, primeFactors := [2, 5, 13, 23] },
    .lucas { root := 7, primeFactors := [2, 3, 5, 32191] },
    .lucas { root := 6, primeFactors := [2, 3, 5, 29, 37] }])

private theorem prime_11217 : Nat.Prime 3999999999999988783 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 7, 1051, 7793, 13327, 290837] },
    .lucas { root := 7, primeFactors := [2, 3, 5, 7] },
    .lucas { root := 3, primeFactors := [2, 487] },
    .lucas { root := 3, primeFactors := [2, 3, 2221] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 37] },
    .lucas { root := 3, primeFactors := [2, 7, 13, 17, 47] }])

private theorem prime_212453 : Nat.Prime 3999999999999787547 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 7, 79, 89, 1429, 3761, 1080143] },
    .lucas { root := 6, primeFactors := [2, 3, 7, 17] },
    .lucas { root := 3, primeFactors := [2, 5, 47] },
    .lucas { root := 5, primeFactors := [2, 7, 77153] },
    .lucas { root := 3, primeFactors := [2, 2411] },
    .lucas { root := 6, primeFactors := [2, 5, 241] }])

private theorem prime_143871 : Nat.Prime 3999999999999856129 := by
  primality (cert := .witnesses [
    .lucas { root := 11, primeFactors := [2, 3, 19, 31, 83, 139, 14461, 26501] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 241] },
    .lucas { root := 2, primeFactors := [2, 5, 53] }])

private theorem prime_83387 : Nat.Prime 3999999999999916613 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 7, 23, 97, 1559, 12757, 65707] },
    .lucas { root := 19, primeFactors := [2, 19, 41] },
    .lucas { root := 2, primeFactors := [2, 3, 1063] },
    .lucas { root := 3, primeFactors := [2, 3, 59] },
    .lucas { root := 2, primeFactors := [2, 3, 47, 233] }])

private theorem prime_69849 : Nat.Prime 3999999999999930151 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 5, 7, 211, 3301, 4283, 1277011] },
    .lucas { root := 6, primeFactors := [2, 3, 5, 11] },
    .lucas { root := 2, primeFactors := [2, 2141] },
    .lucas { root := 2, primeFactors := [2, 5, 107] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 7, 2027] },
    .lucas { root := 2, primeFactors := [2, 1013] }])

private theorem prime_138293 : Nat.Prime 3999999999999861707 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 317, 401, 2749, 6779, 844279] },
    .lucas { root := 6, primeFactors := [2, 3, 229] },
    .lucas { root := 2, primeFactors := [2, 3389] },
    .lucas { root := 3, primeFactors := [2, 7, 11] },
    .lucas { root := 3, primeFactors := [2, 3, 223, 631] }])

private theorem prime_173901 : Nat.Prime 3999999999999826099 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 3, 17, 53, 79, 12401, 4750103] },
    .lucas { root := 3, primeFactors := [2, 5, 31] },
    .lucas { root := 5, primeFactors := [2, 7, 47, 7219] },
    .lucas { root := 2, primeFactors := [2, 3, 401] }])

private theorem prime_65999 : Nat.Prime 3999999999999934001 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 5, 7, 23, 31, 47, 3019, 2824109] },
    .lucas { root := 2, primeFactors := [2, 3, 503] },
    .lucas { root := 2, primeFactors := [2, 7, 17, 349] }])

private theorem prime_80831 : Nat.Prime 3999999999999919169 := by
  primality (cert := .witnesses [
    .lucas { root := 6, primeFactors := [2, 11, 241, 827, 16381, 1740301] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 7, 13] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 5801] },
    .lucas { root := 3, primeFactors := [2, 5, 29] }])

private theorem prime_78273 : Nat.Prime 3999999999999921727 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 313, 433, 5119, 13913, 69067] },
    .lucas { root := 3, primeFactors := [2, 3, 853] },
    .lucas { root := 3, primeFactors := [2, 37, 47] },
    .lucas { root := 2, primeFactors := [2, 3, 1279] },
    .lucas { root := 3, primeFactors := [2, 3, 71] }])

private theorem prime_6399 : Nat.Prime 3999999999999993601 := by
  primality (cert := .witnesses [
    .lucas { root := 19, primeFactors := [2, 3, 5, 13, 29, 1667, 4999, 5101] },
    .lucas { root := 2, primeFactors := [2, 7, 17] },
    .lucas { root := 3, primeFactors := [2, 3, 7, 17] },
    .lucas { root := 6, primeFactors := [2, 3, 5, 17] }])

private theorem prime_53297 : Nat.Prime 3999999999999946703 := by
  primality (cert := .witnesses [
    .lucas { root := 5, primeFactors := [2, 5231, 23687, 23773, 678971] },
    .lucas { root := 7, primeFactors := [2, 5, 523] },
    .lucas { root := 5, primeFactors := [2, 13, 911] },
    .lucas { root := 5, primeFactors := [2, 3, 7, 283] },
    .lucas { root := 2, primeFactors := [2, 5, 43, 1579] },
    .lucas { root := 3, primeFactors := [2, 3, 263] }])

private theorem prime_59333 : Nat.Prime 3999999999999940667 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 61, 109, 193, 1621, 9011, 106699] },
    .lucas { root := 2, primeFactors := [2, 3, 5] },
    .lucas { root := 2, primeFactors := [2, 5, 17, 53] },
    .lucas { root := 3, primeFactors := [2, 3, 17783] },
    .lucas { root := 5, primeFactors := [2, 17, 523] }])

private theorem prime_1959 : Nat.Prime 3999999999999998041 := by
  primality (cert := .witnesses [
    .lucas { root := 14, primeFactors := [2, 3, 5, 78427, 425023695071] },
    .lucas { root := 3, primeFactors := [2, 3, 4357] },
    .lucas { root := 2, primeFactors := [2, 3, 11] },
    .lucas { root := 34, primeFactors := [2, 5, 13, 23, 142148393] },
    .lucas { root := 3, primeFactors := [2, 31, 573179] },
    .lucas { root := 2, primeFactors := [2, 286589] },
    .lucas { root := 2, primeFactors := [2, 71647] },
    .lucas { root := 3, primeFactors := [2, 3, 11941] },
    .lucas { root := 10, primeFactors := [2, 3, 5, 199] }])

private theorem prime_3663 : Nat.Prime 3999999999999996337 := by
  primality (cert := .witnesses [
    .lucas { root := 10, primeFactors := [2, 3, 17, 1038043, 4722309947] },
    .lucas { root := 2, primeFactors := [2, 3, 47, 409] },
    .lucas { root := 2, primeFactors := [2, 17, 29, 67, 71483] },
    .lucas { root := 2, primeFactors := [2, 103, 347] }])

private theorem prime_1631 : Nat.Prime 3999999999999998369 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 11, 37, 277, 17921, 5624461] },
    .lucas { root := 3, primeFactors := [2, 5, 7] },
    .lucas { root := 7, primeFactors := [2, 3, 5, 31247] },
    .lucas { root := 5, primeFactors := [2, 17, 919] }])

private theorem prime_1851 : Nat.Prime 3999999999999998149 := by
  primality (cert := .witnesses [
    .lucas { root := 6, primeFactors := [2, 3, 7, 11, 618429189857761] },
    .lucas { root := 11, primeFactors := [2, 3, 5, 593, 724223803] },
    .lucas { root := 7, primeFactors := [2, 3, 43, 73, 38453] },
    .lucas { root := 2, primeFactors := [2, 9613] },
    .lucas { root := 2, primeFactors := [2, 3, 89] }])

private theorem prime_3389 : Nat.Prime 3999999999999996611 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 5, 2693, 148533234311177] },
    .lucas { root := 2, primeFactors := [2, 673] },
    .lucas { root := 3, primeFactors := [2, 11, 13, 17, 8111, 941617] },
    .lucas { root := 11, primeFactors := [2, 5, 811] },
    .lucas { root := 15, primeFactors := [2, 3, 13, 503] }])

private theorem prime_5187 : Nat.Prime 3999999999999994813 := by
  primality (cert := .witnesses [
    .lucas { root := 6, primeFactors := [2, 3, 23, 199, 2697329913119] },
    .lucas { root := 7, primeFactors := [2, 1348664956559] },
    .lucas { root := 7, primeFactors := [2, 569, 1185118591] },
    .lucas { root := 3, primeFactors := [2, 3, 5, 39503953] },
    .lucas { root := 5, primeFactors := [2, 3, 274333] },
    .lucas { root := 2, primeFactors := [2, 3, 22861] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 127] }])

private theorem prime_5063 : Nat.Prime 3999999999999994937 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 11, 45454545454545397] },
    .lucas { root := 6, primeFactors := [2, 3, 13, 2243, 43301425379] },
    .lucas { root := 2, primeFactors := [2, 19, 59] },
    .lucas { root := 2, primeFactors := [2, 37, 53, 379, 29131] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 971] }])

private theorem prime_2211 : Nat.Prime 3999999999999997789 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 3, 333333333333333149] },
    .lucas { root := 2, primeFactors := [2, 29, 37, 77663870767319] },
    .lucas { root := 7, primeFactors := [2, 11, 101, 337, 103715837] },
    .lucas { root := 2, primeFactors := [2, 7, 3704137] },
    .lucas { root := 5, primeFactors := [2, 3, 154339] },
    .lucas { root := 3, primeFactors := [2, 3, 29, 887] }])

private theorem prime_2813 : Nat.Prime 3999999999999997187 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 17, 117647058823529329] },
    .lucas { root := 7, primeFactors := [2, 3, 61, 5393, 15329, 162011] },
    .lucas { root := 3, primeFactors := [2, 337] },
    .lucas { root := 3, primeFactors := [2, 479] },
    .lucas { root := 2, primeFactors := [2, 5, 17, 953] }])

private theorem prime_3167 : Nat.Prime 3999999999999996833 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 7, 17857142857142843] },
    .lucas { root := 2, primeFactors := [2, 11, 17, 47746371275783] },
    .lucas { root := 5, primeFactors := [2, 17, 59, 23801780297] },
    .lucas { root := 3, primeFactors := [2, 7, 163, 2607557] },
    .lucas { root := 2, primeFactors := [2, 7, 23, 4049] },
    .lucas { root := 3, primeFactors := [2, 11, 23] }])

private theorem prime_3603 : Nat.Prime 3999999999999996397 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 3, 111111111111111011] },
    .lucas { root := 2, primeFactors := [2, 5, 11111111111111101] },
    .lucas { root := 6, primeFactors := [2, 3, 5, 31, 37, 41, 271, 2906161] },
    .lucas { root := 7, primeFactors := [2, 3, 5, 12109] },
    .lucas { root := 6, primeFactors := [2, 3, 1009] }])

def offsets : List ℕ :=
  [2847, 10403, 8949, 57071, 15077, 24621, 7199, 13923, 18117, 67583, 59751, 68609, 88623, 42857, 135221, 36099, 77099, 137733, 72683, 180381, 21647, 109899, 130751, 96417, 154643, 225219, 175737, 214319, 245771, 223701, 197163, 145967, 203699, 191103, 113963, 90447, 132663, 39647, 188079, 204491, 113129, 233241, 13547, 182783, 11217, 212453, 143871, 83387, 69849, 138293, 173901, 65999, 80831, 78273, 6399, 53297, 59333, 1959, 3663, 1631, 1851, 3389, 5187, 5063, 2211, 2813, 3167, 3603]

private def certifiedOffsets : List {s : ℕ // (4000000000000000000-s).Prime} :=
  [⟨2847, prime_2847⟩,
   ⟨10403, prime_10403⟩,
   ⟨8949, prime_8949⟩,
   ⟨57071, prime_57071⟩,
   ⟨15077, prime_15077⟩,
   ⟨24621, prime_24621⟩,
   ⟨7199, prime_7199⟩,
   ⟨13923, prime_13923⟩,
   ⟨18117, prime_18117⟩,
   ⟨67583, prime_67583⟩,
   ⟨59751, prime_59751⟩,
   ⟨68609, prime_68609⟩,
   ⟨88623, prime_88623⟩,
   ⟨42857, prime_42857⟩,
   ⟨135221, prime_135221⟩,
   ⟨36099, prime_36099⟩,
   ⟨77099, prime_77099⟩,
   ⟨137733, prime_137733⟩,
   ⟨72683, prime_72683⟩,
   ⟨180381, prime_180381⟩,
   ⟨21647, prime_21647⟩,
   ⟨109899, prime_109899⟩,
   ⟨130751, prime_130751⟩,
   ⟨96417, prime_96417⟩,
   ⟨154643, prime_154643⟩,
   ⟨225219, prime_225219⟩,
   ⟨175737, prime_175737⟩,
   ⟨214319, prime_214319⟩,
   ⟨245771, prime_245771⟩,
   ⟨223701, prime_223701⟩,
   ⟨197163, prime_197163⟩,
   ⟨145967, prime_145967⟩,
   ⟨203699, prime_203699⟩,
   ⟨191103, prime_191103⟩,
   ⟨113963, prime_113963⟩,
   ⟨90447, prime_90447⟩,
   ⟨132663, prime_132663⟩,
   ⟨39647, prime_39647⟩,
   ⟨188079, prime_188079⟩,
   ⟨204491, prime_204491⟩,
   ⟨113129, prime_113129⟩,
   ⟨233241, prime_233241⟩,
   ⟨13547, prime_13547⟩,
   ⟨182783, prime_182783⟩,
   ⟨11217, prime_11217⟩,
   ⟨212453, prime_212453⟩,
   ⟨143871, prime_143871⟩,
   ⟨83387, prime_83387⟩,
   ⟨69849, prime_69849⟩,
   ⟨138293, prime_138293⟩,
   ⟨173901, prime_173901⟩,
   ⟨65999, prime_65999⟩,
   ⟨80831, prime_80831⟩,
   ⟨78273, prime_78273⟩,
   ⟨6399, prime_6399⟩,
   ⟨53297, prime_53297⟩,
   ⟨59333, prime_59333⟩,
   ⟨1959, prime_1959⟩,
   ⟨3663, prime_3663⟩,
   ⟨1631, prime_1631⟩,
   ⟨1851, prime_1851⟩,
   ⟨3389, prime_3389⟩,
   ⟨5187, prime_5187⟩,
   ⟨5063, prime_5063⟩,
   ⟨2211, prime_2211⟩,
   ⟨2813, prime_2813⟩,
   ⟨3167, prime_3167⟩,
   ⟨3603, prime_3603⟩]

/-- Lucas certificates establish primality of every large summand. -/
theorem anchors_prime (a : ℕ) (ha : a ∈ offsets) : Nat.Prime (4000000000000000000 - a) := by
  have hm : a ∈ certifiedOffsets.map Subtype.val := ha
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hm
  exact s.property


end PostBoundary524288.Anchors

/-! An exact finite Goldbach cover using a checked sieve of bit positions.
A geometric series proposes a mask of multiples. The kernel verifies its
first bit and translation closure, which suffice for the primality proof. -/

namespace PostBoundary524288.Cover

/-- Bits at indices less than `width`. -/
def lowMask (width : ℕ) : ℕ := (1 <<< width) - 1

theorem lowMask_bit (width i : ℕ) : (lowMask width).testBit i = decide (i < width) := by
  simp [lowMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]

/-- A mask passes if it contains zero and shifting a live bit by `step`
preserves it whenever the resulting position is below `width`. -/
def advances (width step bits : ℕ) : Bool :=
  let moved := (bits <<< step) &&& lowMask width
  bits.testBit 0 && ((moved &&& bits) == moved)

theorem multiples_in_mask {width step bits : ℕ} (h : advances width step bits = true)
    (k : ℕ) (hk : step * k < width) : bits.testBit (step * k) = true := by
  simp only [advances, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hz, hs'⟩ := h
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    have hle : step * k ≤ step * (k + 1) := Nat.mul_le_mul_left step (Nat.le_succ k)
    have hprev := ih (lt_of_le_of_lt hle hk)
    have hge : step ≤ step * (k + 1) := by rw [Nat.mul_succ]; omega
    have hsub : step * (k + 1) - step = step * k := by rw [Nat.mul_succ]; omega
    have hm : ((bits <<< step) &&& lowMask width).testBit (step * (k+1)) = true := by
      simp [Nat.testBit_and, Nat.testBit_shiftLeft, lowMask_bit, hk, hge, hsub, hprev]
    have hi := congrArg (fun m : ℕ => m.testBit (step * (k + 1))) hs'
    change ((((bits <<< step) &&& lowMask width) &&& bits).testBit _) =
      (((bits <<< step) &&& lowMask width).testBit _) at hi
    rwa [Nat.testBit_and, hm, Bool.true_and] at hi

def unionBy {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: rest => f a ||| unionBy f rest

theorem unionBy_bit {α : Type} (f : α → ℕ) (xs : List α) (i : ℕ) :
    (unionBy f xs).testBit i = true ↔ ∃ x ∈ xs, (f x).testBit i = true := by
  induction xs with
  | nil => simp [unionBy]
  | cons x xs ih => simp [unionBy, Nat.testBit_or, ih]

/-- The denominator is odd and positive when `d ≥ 2`. The proofs below
only need the checked closure property of this proposed periodic pattern. -/
def period (width d : ℕ) : ℕ :=
  lowMask ((width / d + 1) * d) / lowMask d

def divisors : List ℕ := ((List.range 876).map (· + 2)).filter (fun d => decide d.Prime)
def width : ℕ := 770060

def survivors : ℕ := lowMask width ^^^ unionBy (period width) divisors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem periods_checked : divisors.all (fun d => advances width d (period width d)) = true := by
  decide +kernel

theorem survivors_prime {q : ℕ} (hq : 2 ≤ q) (hlt : q < width)
    (hb : survivors.testBit q = true) : Nat.Prime q := by
  by_contra hcomp
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < q) hcomp
  have hlo := (Nat.minFac_prime (by omega : q ≠ 1)).two_le
  have hupper : q.minFac < 878 := by
    by_contra! hlarge
    have hone := Nat.mul_le_mul hlarge hlarge
    rw [pow_two] at hsq
    change q < 770060 at hlt
    omega
  have hd : q.minFac ∈ divisors := by
    refine List.mem_filter.mpr ⟨?_, decide_eq_true (Nat.minFac_prime (by omega))⟩
    apply List.mem_map.mpr
    exact ⟨q.minFac - 2, List.mem_range.mpr (by omega), by omega⟩
  have hcheck := (List.all_eq_true.mp periods_checked) q.minFac hd
  obtain ⟨k, hdiv⟩ := Nat.minFac_dvd q
  have hp := multiples_in_mask hcheck k (by simpa only [← hdiv] using hlt)
  rw [← hdiv] at hp
  have hbad := (unionBy_bit (period width) divisors q).2 ⟨q.minFac, hd, hp⟩
  simp [survivors, Nat.testBit_xor, lowMask_bit, hlt, hbad] at hb

end PostBoundary524288.Cover

/-! A contiguous interval of binary Goldbach representations above 4 × 10¹⁸.
The large summands come from Lucas certificates. The small summands come
from the packed sieve proved sound above. -/

namespace PostBoundary524288.Cover

open PostBoundary524288.Anchors (offsets)

/-- A set bit at position j supplies a prime complement for offset 262146+j. -/
def targetBits : ℕ := unionBy (fun a => survivors >>> (a + 262146)) offsets

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem targets_checked : advances 262144 2 targetBits = true := by
  decide +kernel

private theorem offset_bound {a : ℕ} (h : a ∈ offsets) : a ≤ 245771 := by
  have checked : offsets.all (fun v => decide (v ≤ 245771)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked a h)

theorem block (n : ℕ) (lo : 4000000000000262146 ≤ n)
    (hi : n < 4000000000000524290) (even : 2 ∣ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  obtain ⟨half, hhalf⟩ := even
  let k := half - 2000000000000131073
  have heq : n = 4000000000000000000 + 262146 + 2 * k := by dsimp [k]; omega
  have hpos : 2 * k < 262144 := by omega
  have hbit := multiples_in_mask targets_checked k hpos
  obtain ⟨a, ha, hsmall⟩ := (unionBy_bit _ offsets (2 * k)).1 hbit
  rw [Nat.testBit_shiftRight] at hsmall
  have hab := offset_bound ha
  have hp := PostBoundary524288.Anchors.anchors_prime a ha
  have hq := survivors_prime (q := a + 262146 + 2 * k) (by omega)
    (by change _ < 770060; omega) hsmall
  exact ⟨4000000000000000000-a, a+262146+2*k, hp, hq, by omega⟩

end PostBoundary524288.Cover

/-- All 131072 even offsets in the third post-boundary block have prime pairs. -/
theorem Conjectures.Goldbach.FinitePostBoundaryThrough524288 :
    (fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (4*10^18+262146) (4*10^18+524290) :=
  PostBoundary524288.Cover.block
