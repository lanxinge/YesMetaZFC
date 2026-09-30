import YesMetaZFC.SetTheory.Filter.Internal

/-! # 集合编码偏序的内部 MacNeille 切割

切割、切割全体及内部集合族的上确界均由 ZF 幂集和分离构造。
只量化模型中的集合，不把外部谓词幂集或外部完备性偷换为内部完备性。
-/

namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project FilterZF
universe u
variable {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}

def Bound_d (𝕀 : 𝒞.Interpretation ℳ) (B R S a : ℳ.Domain) : Prop :=
  ∀ b, ℳ.mem b B → (∀ c, ℳ.mem c S → ℳ.PairMember 𝕀 c b R) → ℳ.PairMember 𝕀 a b R

def Cut_d (𝕀 : 𝒞.Interpretation ℳ) (B R I : ℳ.Domain) : Prop :=
  Subset_d (ℳ := ℳ) I B ∧ ∀ a, ℳ.mem a B → Bound_d 𝕀 B R I a → ℳ.mem a I

def bound_m (𝒞 : OrderedPairConvention) {n : Nat} (B R S a : Term n) : Formula 1 n :=
  .forallE (.imp (.mem .newest B.weaken) (.imp
    (.forallE (.imp (.mem .newest S.weaken.weaken)
      (Formula.orderedPairMem 𝒞 .newest (.bound 1) R.weaken.weaken)))
    (Formula.orderedPairMem 𝒞 a.weaken .newest R.weaken)))

derive_free_closed bound_m

def cut_m (𝒞 : OrderedPairConvention) {n : Nat} (B R I : Term n) : Formula 1 n :=
  .conj (Formula.subset I B) (.forallE (.imp (.mem .newest B.weaken)
    (.imp (bound_m 𝒞 B.weaken R.weaken I.weaken .newest) (.mem .newest I.weaken))))

derive_free_closed cut_m

theorem bound_sat_d (𝕀 : 𝒞.Interpretation ℳ) {n : Nat} (e : Env ℳ n)
    (B R S a : Term n) : Formula.satisfies e (bound_m 𝒞 B R S a) ↔
      Bound_d 𝕀 (B.eval e) (R.eval e) (S.eval e) (a.eval e) := by
  simp only [bound_m, Bound_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff 𝕀,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken, Term.eval_bound_one_push,
    Term.eval_bound_zero_push]

theorem cut_sat_d (𝕀 : 𝒞.Interpretation ℳ) {n : Nat} (e : Env ℳ n)
    (B R I : Term n) : Formula.satisfies e (cut_m 𝒞 B R I) ↔
      Cut_d 𝕀 (B.eval e) (R.eval e) (I.eval e) := by
  simp only [cut_m, Cut_d, Subset_d, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, bound_sat_d 𝕀,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

def closure_m (𝒞 : OrderedPairConvention) : UnarySchema 3 where
  body := bound_m 𝒞 (.bound 3) (.bound 2) (.bound 1) (.bound 0)

def completion_m (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := cut_m 𝒞 (.bound 2) (.bound 1) (.bound 0)

theorem closure_exists_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    (B R S : ℳ.Domain) : ∃ I, Cut_d 𝕀 B R I ∧
      ∀ a, ℳ.mem a I ↔ ℳ.mem a B ∧ Bound_d 𝕀 B R S a := by
  let e : Env ℳ 3 := ⟨fun i => if i = 0 then S else if i = 1 then R else B, fun _ => B⟩
  obtain ⟨I, hI⟩ := ZF.separation_exists_d hZF (closure_m 𝒞) e B
  have h : ∀ a, ℳ.mem a I ↔ ℳ.mem a B ∧ Bound_d 𝕀 B R S a := by
    intro a
    rw [hI]
    simp only [closure_m, bound_sat_d 𝕀, Term.eval_bound]
    rfl
  refine ⟨I, ⟨fun a ha => ((h a).mp ha).1, fun a ha k => (h a).mpr ⟨ha, ?_⟩⟩, h⟩
  intro b hb hS
  exact k b hb (fun c hc => ((h c).mp hc).2 b hb hS)

/-- 切割全体是内部幂集的可定义子集。 -/
theorem completion_exists_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    (B R : ℳ.Domain) : ∃ K, ∀ I, ℳ.mem I K ↔ Cut_d 𝕀 B R I := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let e : Env ℳ 2 := ⟨fun i => if i = 0 then R else B, fun _ => B⟩
  obtain ⟨K, hK⟩ := ZF.separation_exists_d hZF (completion_m 𝒞) e P
  refine ⟨K, fun I => ?_⟩
  rw [hK, hP]
  have h : Formula.satisfies (e.push I) (completion_m 𝒞).body ↔ Cut_d 𝕀 B R I := by
    simp only [completion_m, cut_sat_d 𝕀, Term.eval_bound]
    rfl
  rw [h]
  exact ⟨fun k => k.2, fun k => ⟨k.1, k⟩⟩

/-- 完备性的量词是内部集合族；上确界仍为内部切割。 -/
theorem sup_exists_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    {B R K : ℳ.Domain} (hK : ∀ I, ℳ.mem I K ↔ Cut_d 𝕀 B R I)
    (S : ℳ.Domain) (hS : Subset_d (ℳ := ℳ) S K) :
    ∃ J, ℳ.mem J K ∧ (∀ I, ℳ.mem I S → Subset_d (ℳ := ℳ) I J) ∧
      ∀ L, ℳ.mem L K → (∀ I, ℳ.mem I S → Subset_d (ℳ := ℳ) I L) →
        Subset_d (ℳ := ℳ) J L := by
  obtain ⟨U, hU⟩ := KP.exists_union (ZF.modelsKP hZF) S
  obtain ⟨J, hJ, h⟩ := closure_exists_d 𝕀 hZF B R U
  refine ⟨J, (hK J).mpr hJ, ?_, ?_⟩
  · intro I hI a ha
    exact (h a).mpr ⟨((hK I).mp (hS I hI)).1 a ha,
      fun b _ hb => hb a ((hU a).mpr ⟨I, hI, ha⟩)⟩
  · intro L hL k a ha
    obtain ⟨hab, habound⟩ := (h a).mp ha
    apply ((hK L).mp hL).2 a hab
    intro b hb hl
    apply habound b hb
    intro c hc
    obtain ⟨I, hI, hcI⟩ := (hU c).mp hc
    exact hl c (k I hI c hcI)

structure Order_d (𝕀 : 𝒞.Interpretation ℳ) (B R : ℳ.Domain) : Prop where
  refl : ∀ a, ℳ.mem a B → ℳ.PairMember 𝕀 a a R
  trans : ∀ a b c, ℳ.mem a B → ℳ.mem b B → ℳ.mem c B →
    ℳ.PairMember 𝕀 a b R → ℳ.PairMember 𝕀 b c R → ℳ.PairMember 𝕀 a c R
  antisymm : ∀ a b, ℳ.mem a B → ℳ.mem b B →
    ℳ.PairMember 𝕀 a b R → ℳ.PairMember 𝕀 b a R → a = b

def principal_m (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := Formula.orderedPairMem 𝒞 (.bound 0) (.bound 1) (.bound 2)

theorem principal_exists_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    {B R : ℳ.Domain} {a : ℳ.Domain} (ha : ℳ.mem a B) :
    ∃ I, Cut_d 𝕀 B R I ∧ ∀ b, ℳ.mem b I ↔ ℳ.mem b B ∧ ℳ.PairMember 𝕀 b a R := by
  let e : Env ℳ 2 := ⟨fun i => if i = 0 then a else R, fun _ => B⟩
  obtain ⟨I, hI⟩ := ZF.separation_exists_d hZF (principal_m 𝒞) e B
  have h : ∀ b, ℳ.mem b I ↔ ℳ.mem b B ∧ ℳ.PairMember 𝕀 b a R := by
    intro b
    rw [hI]
    simp only [principal_m, Formula.satisfies_orderedPairMem_iff 𝕀, Term.eval_bound]
    rfl
  exact ⟨I, ⟨fun b hb => ((h b).mp hb).1, fun b hb k =>
    (h b).mpr ⟨hb, k a ha (fun c hc => ((h c).mp hc).2)⟩⟩, h⟩

theorem principal_order_d (𝕀 : 𝒞.Interpretation ℳ) {B R a b I J : ℳ.Domain}
    (hR : Order_d 𝕀 B R) (ha : ℳ.mem a B) (hb : ℳ.mem b B)
    (hI : ∀ c, ℳ.mem c I ↔ ℳ.mem c B ∧ ℳ.PairMember 𝕀 c a R)
    (hJ : ∀ c, ℳ.mem c J ↔ ℳ.mem c B ∧ ℳ.PairMember 𝕀 c b R) :
    Subset_d (ℳ := ℳ) I J ↔ ℳ.PairMember 𝕀 a b R := by
  constructor
  · intro h
    exact ((hJ a).mp (h a ((hI a).mpr ⟨ha, hR.refl a ha⟩))).2
  · intro h c hc
    obtain ⟨hcB, hca⟩ := (hI c).mp hc
    exact (hJ c).mpr ⟨hcB, hR.trans c a b hcB ha hb hca h⟩

theorem cut_lower_d (𝕀 : 𝒞.Interpretation ℳ) {B R I a b : ℳ.Domain}
    (hR : Order_d 𝕀 B R) (hI : Cut_d 𝕀 B R I) (ha : ℳ.mem a B)
    (hb : ℳ.mem b I) (h : ℳ.PairMember 𝕀 a b R) : ℳ.mem a I :=
  hI.2 a ha (fun c hc k => hR.trans a b c ha (hI.1 b hb) hc h (k b hb))

end YesMetaZFC.SetTheory.BooleanZF
