%default total 

data MN = MZ | MS MN 

(+) : MN -> MN -> MN
MZ + y = y
(MS x) + y = MS $ x + y

(-) : MN -> MN -> MN
MZ - _ = MZ
x - MZ = x
(MS x) - (MS y) = x - y

(*) : MN -> MN -> MN
MZ * _ = MZ
(MS x) * y = y + (x * y)

data Mle : (n, m : MN) -> Type where
  Mlz : Mle MZ m 
  Mls : Mle n m -> Mle (MS n) (MS m)

example : (a, b : MN) -> Mle a b -> a - b = MZ
example MZ x prf = Refl
example (MS x) (MS y) (Mls prf) = rewrite example x y prf in Refl

zero_plus_com : (a : MN) -> a + MZ = a
zero_plus_com MZ = Refl
zero_plus_com (MS a) = rewrite zero_plus_com a in Refl

succ_plus_com : (a, b : MN) -> a + MS b = MS (a + b)
succ_plus_com MZ b = Refl
succ_plus_com (MS a) b = rewrite succ_plus_com a b in Refl

succ_plus_com2 : (a, b : MN) -> MS (a + b) = a + MS b 
succ_plus_com2 MZ b = Refl
succ_plus_com2 (MS a) b = rewrite succ_plus_com a b in Refl

com_plus : (a, b : MN) -> a + b = b + a
com_plus MZ b = rewrite zero_plus_com b in Refl
com_plus (MS a) b = rewrite com_plus a b in rewrite succ_plus_com b a in Refl

assoc_plus : (a, b, c: MN) -> (a + b) + c = a + (b + c)
assoc_plus MZ _ _ = Refl
assoc_plus (MS a) b c = rewrite assoc_plus a b c in Refl

left_dist : (a, b, c: MN) -> (a + b) * c = a * c + b * c
left_dist MZ _ _ = Refl
left_dist (MS a) b c = rewrite left_dist a b c in rewrite assoc_plus c (a * c) (b * c) in Refl

lem : (a, b, c, d: MN) -> a + b + (c + d) = a + b + c + d
lem a b c d = rewrite assoc_plus (a + b) c d in Refl

lem2 : (a, b, c, d: MN) -> a + b + c + d = a + c + b + d
lem2 MZ b c d = rewrite com_plus b c in Refl
lem2 (MS a) b c d = rewrite lem2 a b c d in Refl

right_dist : (a, b, c: MN) -> a * (b + c) = a * b + a * c
right_dist MZ _ _ = Refl
right_dist (MS a) b c = rewrite right_dist a b c in 
  rewrite lem b (a * b) c (a * c) in
    rewrite lem2 b (a * b) c (a * c) in 
      rewrite lem b c (a * b) (a * c) in 
        Refl

lem3 : (a, b, c, d: MN) -> (a + b) * (c + d) = a * (c + d) + b * (c + d)
lem3 a b c d = left_dist a b (c + d)

lem4 : (a, b, c, d: MN) -> a * (c + d) + b * (c + d) = a * c + a * d + b * c + b * d
lem4 a b c d = rewrite right_dist a c d in 
 rewrite right_dist b c d in 
  rewrite lem (a * c) (a * d) (b * c) (b * d) in 
   Refl

lem5 : (a, b : MN) -> (a + b) * (a + b) = a * a + a * b + b * a + b * b
lem5 a b = rewrite lem3 a b a b in 
 rewrite lem4 a b a b in 
  Refl

f1Lem : (a, b : MN) -> Mle a b -> Mle (a - b) (a + b)
f1Lem MZ y prf = Mlz
f1Lem (MS x) (MS y) (Mls prf) = rewrite example x y prf in Mlz

first : (a, b : MN) -> Mle a b -> Mle ((a - b) * (a - b)) ((a + b) * (a + b))
first MZ y prf = Mlz
first (MS x) (MS y) (Mls prf) = rewrite example x y prf in Mlz

second : (a, b : MN) -> Mle (a * b + a * b) ((a + b) * (a + b))
second MZ y = Mlz
second (MS x) y = Mlz -- Далее тут нужно доказать, что a * b + a * b = MZ, но как? 

third : (a, b, c : MN) -> Mle a b -> Mle b c -> a = c -> a = b
fourth :  (a, b : MN) -> a * b + (c + e) * d = d * c + a * b + e * d

fifth : (a, b : MN) -> Mle (a * a + b * b) ((a + b) * (a + b))
fifth MZ MZ = Mlz
fifth (MS x) (MS y) = Mlz -- Далее тут нужно доказать, что a * a + b * b = MZ, но как? 

main : IO ()
main = print 1