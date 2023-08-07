import tactic
import algebra.category.Group 
import data.set.pointwise
import algebra.char_p
import data.zmod.basic
import algebra.category.CommRing.basic
import data.opposite

lemma lin {l m n : ℕ }(lm : l > m) (mn : m>n) : (l > n):=
begin
  linarith,
end

@[ext] structure inverse_group_system:=
(to_group : ℕ → Group)
(to_hom {m n : ℕ} (mn:m>n) : (to_group m) →* (to_group n) )
(comp {l m n : ℕ} (lm : l > m) (mn : m>n) : monoid_hom.comp (to_hom mn) (to_hom lm) = to_hom (lin lm mn))
instance : has_coe inverse_group_system (ℕ → Group):=
{ coe := inverse_group_system.to_group }

def to_set (g:Group): set g:=
begin
  exact {a : g | true}
end

variable s:inverse_group_system
def Mittag_Leffler_condition (S:inverse_group_system):Prop :=
  ∀ a:ℕ, ∃ (b:ℕ) (ba : b>a), ∀ c:ℕ, b≥c ∨ 
    ∃ cb: c>b, set.image (S.to_hom ba).to_fun (to_set (S.to_group b)) = 
               set.image (S.to_hom (lin cb ba)) (to_set (S.to_group c))



               

def p_adic_ring (p : ℕ) : ℕᵒᵖ → Ring := λ n, (Ring.of (zmod (p^(opposite.unop n))))

def p_adic_hom (p n m : ℕ) (c: n≥m): (Ring.of (zmod (p ^ n))) ⟶ (Ring.of (zmod (p ^ m))):=
begin
  exact Ring.of_hom (zmod.cast_hom (pow_dvd_pow p c) (zmod (p^m))),
end 

def p_adic_hom_other (p n m : ℕ) (c: n≥m): zmod (p ^ n) →+* zmod (p ^ m):=
begin
  exact zmod.cast_hom (pow_dvd_pow p c) (zmod (p^m)),
end 

def p_addic_functor_other (p:ℕ) : ℕᵒᵖ ⥤ Ring :=
{ obj:=p_adic_ring p,
  map:=λ x y h, p_adic_hom_other p (opposite.unop x) (opposite.unop y) (ge.le (category_theory.le_of_op_hom h))
}

def p_addic_functor (p:ℕ) : ℕᵒᵖ ⥤ Ring :=
{ obj:=p_adic_ring p,
  map:=
    begin
      intros x y,
      intro h,
      set myx:= (opposite.unop x),
      set myy:= (opposite.unop y),
      have t: myy≤myx := category_theory.le_of_op_hom h,
      rw p_adic_ring,
      dsimp,
      have d:= p_adic_hom_other p myx myy (ge.le t),
      split,
      exact d.map_one',
      exact d.map_mul',
      exact d.map_zero',
      exact d.map_add',
    end
}