import Mathlib

#check Complex.conj_I

open Complex

open scoped ComplexConjugate

variable (a : ℂ ) (b : ℂ ) (z : ℂ )
#check  RCLike.conj_eq_re_sub_im 

example (z : ℂ) (a : ℂ ) : conj (z + a) = conj z + conj a := star_add z a







example (z : ℂ) : Complex.re z = (1 /2) * (z + conj z) := Complex.ext_iff.mpr (by field_simp)


example : Complex.exp (z * I) = Complex.cos z + Complex.sin z * I := by exact Complex.exp_mul_I z

example : deriv (fun z => Complex.exp (I * z)) z  = I * Complex.exp (I * z) := by 
  rw [deriv_cexp]
  have fun_mul : HMul.hMul I =  (fun y => I * id y) := rfl
  nth_rw 2 [fun_mul]
  have : deriv (fun y ↦ I * id y) z =  I * deriv ( fun y => id y) z := by exact deriv_const_mul_field I
  rw [this]
  rw [deriv_id]
  ring
  fun_prop


#check Complex.differentiableAt_exp
  

#check deriv_comp


  


  



