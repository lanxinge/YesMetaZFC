import YesMetaZFC.SetTheory.Boolean.CompleteHom

/-! # 完备代数及完全同态的原语言公式

用于把同一个内部集合图的性质沿初等模型反射；任意上确界始终量化模型对象。
-/
namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def imp_m (𝒞 : OrderedPairConvention) {n} (B R a b c : Term n) : Formula 1 n := set[n] ⟪
  ⌜c⌝ₛ ∈ ⌜B⌝ₛ ∧ (∀ d ∈ ⌜B⌝ₛ, ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(d,⌜c⌝ₛ,⌜R⌝ₛ) ↔
    (∀ m, ⌜(meet_m 𝒞)⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,d,⌜a⌝ₛ,m) → ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(m,⌜b⌝ₛ,⌜R⌝ₛ)))⟫
derive_free_closed imp_m

theorem imp_sat_l {n} (ρ : Env M n) (B R a b c : Term n) :
    Formula.satisfies ρ (imp_m 𝒞 B R a b c) ↔ Imp_d I (B.eval ρ) (R.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) := by
  simp only [imp_m,Imp_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I,meet_sat_d I,Definitional.Term.eval_weaken]
  rfl

def bsup_m (𝒞 : OrderedPairConvention) {n} (B R A a : Term n) : Formula 1 n := set[n] ⟪
  ⌜a⌝ₛ ∈ ⌜B⌝ₛ ∧ (∀ x ∈ ⌜A⌝ₛ, ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(x,⌜a⌝ₛ,⌜R⌝ₛ)) ∧
  (∀ b ∈ ⌜B⌝ₛ, (∀ x ∈ ⌜A⌝ₛ, ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(x,b,⌜R⌝ₛ)) → ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(⌜a⌝ₛ,b,⌜R⌝ₛ))⟫
derive_free_closed bsup_m

theorem bsup_sat_l {n} (ρ : Env M n) (B R A a : Term n) :
    Formula.satisfies ρ (bsup_m 𝒞 B R A a) ↔ Bsup_d I (B.eval ρ) (R.eval ρ) (A.eval ρ) (a.eval ρ) := by
  simp only [bsup_m,Bsup_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]
  rfl

def cba_m (𝒞 : OrderedPairConvention) {n} (B R z : Term n) : Formula 1 n := set[n] ⟪
  (∀ a ∈ ⌜B⌝ₛ, ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(a,a,⌜R⌝ₛ)) ∧
  (∀ a ∈ ⌜B⌝ₛ, ∀ b ∈ ⌜B⌝ₛ, ∀ c ∈ ⌜B⌝ₛ,
    ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(a,b,⌜R⌝ₛ) → ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(b,c,⌜R⌝ₛ) → ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(a,c,⌜R⌝ₛ)) ∧
  (∀ a ∈ ⌜B⌝ₛ, ∀ b ∈ ⌜B⌝ₛ,
    ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(a,b,⌜R⌝ₛ) → ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(b,a,⌜R⌝ₛ) → a = b) ∧
  ⌜z⌝ₛ ∈ ⌜B⌝ₛ ∧ (∀ a ∈ ⌜B⌝ₛ, ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(⌜z⌝ₛ,a,⌜R⌝ₛ)) ∧
  (∀ a ∈ ⌜B⌝ₛ, ∀ b ∈ ⌜B⌝ₛ, ∃ c, ⌜(meet_m 𝒞)⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,a,b,c)) ∧
  (∀ a ∈ ⌜B⌝ₛ, ∀ b ∈ ⌜B⌝ₛ, ∃ c, ⌜(imp_m 𝒞)⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,a,b,c)) ∧
  (∀ a ∈ ⌜B⌝ₛ, ∀ b, ∀ c, ⌜(imp_m 𝒞)⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,a,⌜z⌝ₛ,b) →
    ⌜(imp_m 𝒞)⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,b,⌜z⌝ₛ,c) → c = a) ∧
  (∀ A, A ⊆ ⌜B⌝ₛ → ∃ a, ⌜(bsup_m 𝒞)⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,A,a))⟫
derive_free_closed cba_m

theorem cba_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z : Term n) :
    Formula.satisfies ρ (cba_m 𝒞 B R z) ↔ Cba_d I (B.eval ρ) (R.eval ρ) (z.eval ρ) := by
  simp only [cba_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE,Formula.satisfies_subset_iff,
    Formula.satisfies_orderedPairMem_iff I,meet_sat_d I,imp_sat_l I,bsup_sat_l I,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨refl,tr,anti,hz,bot,meet,imp,neg,sup⟩
    exact ⟨⟨⟨refl,(fun a b c ha hb hc => tr a ha b hb c hc),
      (fun a b ha hb => anti a ha b hb)⟩,hz,bot,(fun a b ha hb => meet a ha b hb),
      (fun a b ha hb => imp a ha b hb),(fun a b c ha => neg a ha b c)⟩,sup⟩
  · intro h
    exact ⟨h.order.refl,(fun a ha b hb c hc => h.order.trans a b c ha hb hc),
      (fun a ha b hb => h.order.antisymm a b ha hb),h.bot_mem,h.bot_le,
      (fun a ha b hb => h.meet a b ha hb),(fun a ha b hb => h.imp a b ha hb),
      (fun a ha b c => h.double_neg a b c ha),h.sup⟩

def cbh_m (𝒞 : OrderedPairConvention) {n} (B R z C S w F : Term n) : Formula 1 n := set[n] ⟪
  ⌜(Formula.isFunctionFromTo 𝒞)⌝ₚ(⌜F⌝ₛ,⌜B⌝ₛ,⌜C⌝ₛ) ∧ ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(⌜z⌝ₛ,⌜w⌝ₛ,⌜F⌝ₛ) ∧
  (∀ a, ∀ b, ∀ c, ∀ x, ∀ y, ∀ v,
    ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(a,x,⌜F⌝ₛ) → ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(b,y,⌜F⌝ₛ) →
    ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(c,v,⌜F⌝ₛ) → ⌜(meet_m 𝒞)⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,a,b,c) → ⌜(meet_m 𝒞)⌝ₚ(⌜C⌝ₛ,⌜S⌝ₛ,x,y,v)) ∧
  (∀ a, ∀ b, ∀ x, ∀ y,
    ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(a,x,⌜F⌝ₛ) → ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(b,y,⌜F⌝ₛ) →
    ⌜(imp_m 𝒞)⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,a,⌜z⌝ₛ,b) → ⌜(imp_m 𝒞)⌝ₚ(⌜C⌝ₛ,⌜S⌝ₛ,x,⌜w⌝ₛ,y)) ∧
  (∀ A, ∀ a, ∀ x, A ⊆ ⌜B⌝ₛ → ⌜(bsup_m 𝒞)⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,A,a) →
    ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(a,x,⌜F⌝ₛ) →
    (∀ b ∈ A, ∀ y, ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(b,y,⌜F⌝ₛ) → ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(y,x,⌜S⌝ₛ)) ∧
    (∀ d ∈ ⌜C⌝ₛ, (∀ b ∈ A, ∀ y, ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(b,y,⌜F⌝ₛ) → ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(y,d,⌜S⌝ₛ)) →
      ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(x,d,⌜S⌝ₛ)))⟫
derive_free_closed cbh_m

theorem cbh_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z C S w F : Term n) :
    Formula.satisfies ρ (cbh_m 𝒞 B R z C S w F) ↔
      Cbh_d I (B.eval ρ) (R.eval ρ) (z.eval ρ) (C.eval ρ) (S.eval ρ) (w.eval ρ) (F.eval ρ) := by
  simp only [cbh_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_subset_iff,Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_orderedPairMem_iff I,meet_sat_d I,imp_sat_l I,bsup_sat_l I,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨fn,zero,meet,neg,sup⟩
    exact ⟨⟨fn,zero,meet,neg⟩,fun A a x sub h ax =>
      ⟨fun b y hb by' => (sup A a x sub h ax).1 b hb y by',
       fun d hd bound => (sup A a x sub h ax).2 d hd (fun b hb y by' => bound b y hb by')⟩⟩
  · intro h
    exact ⟨h.function,h.zero,h.meet,h.neg,fun A a x sub sup ax =>
      ⟨fun b hb y by' => (h.sup A a x sub sup ax).1 b y hb by',
       fun d hd bound => (h.sup A a x sub sup ax).2 d hd (fun b y hb by' => bound b hb y by')⟩⟩

end YesMetaZFC.SetTheory.BooleanZF
