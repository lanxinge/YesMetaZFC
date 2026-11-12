import YesMetaZFC.Model.Forcing.Stage.Embedding
import YesMetaZFC.Model.Forcing.CCC.Syntax
import YesMetaZFC.SetTheory.Choice

/-! # 模型内部的极大反链选择

按内部序数枚举逐项扫描，只保留与此前保留项不相容的正条件。
递归图和所得反链均属于原模型；不以外部 Zorn 引理代替内部构造。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Ac_pick_d (B R z E F a : M.Domain) : Prop :=
  ∃ i, (∀ j, M.mem j i ↔ ∃ q, Entry_d M j q F) ∧
    Entry_d M i a E ∧ M.mem a B ∧ a ≠ z ∧
      ∀ j q, Entry_d M j q F → q ≠ z → ¬ Cmp_d M B R z a q

def ac_pick_m {n} (B R z E F a : Term n) : Formula 1 n := set[n] ⟪
  ∃ i, (∀ j, j ∈ i ↔ (∃ q, ⌜entry_m⌝ₚ(j,q,⌜F⌝ₛ))) ∧
    ⌜entry_m⌝ₚ(i,⌜a⌝ₛ,⌜E⌝ₛ) ∧ ⌜a⌝ₛ ∈ ⌜B⌝ₛ ∧ ⌜a⌝ₛ ≠ ⌜z⌝ₛ ∧
    (∀ j, ∀ q, ⌜entry_m⌝ₚ(j,q,⌜F⌝ₛ) → q ≠ ⌜z⌝ₛ → ¬ ⌜cmp_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜a⌝ₛ,q))⟫
derive_free_closed ac_pick_m

theorem ac_pick_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z E F a : Term n) :
    Formula.satisfies ρ (ac_pick_m B R z E F a) ↔
      Ac_pick_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (E.eval ρ) (F.eval ρ) (a.eval ρ) := by
  simp only [ac_pick_m,Ac_pick_d,Formula.satisfies_exists_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.extensionalNe,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_imp_iff,entry_sat_l M hE,cmp_sat_l M hE,Definitional.Term.eval_weaken]
  rfl

def Ac_step_d (B R z E F a : M.Domain) : Prop := Ac_pick_d B R z E F a ∨
  (¬ ∃ q, Ac_pick_d B R z E F q) ∧ a = z

def ac_step_m {n} (B R z E F a : Term n) : Formula 1 n := set[n] ⟪
  ⌜ac_pick_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜E⌝ₛ,⌜F⌝ₛ,⌜a⌝ₛ) ∨
  ((¬ (∃ q, ⌜ac_pick_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜E⌝ₛ,⌜F⌝ₛ,q))) ∧ ⌜a⌝ₛ = ⌜z⌝ₛ)⟫
derive_free_closed ac_step_m

theorem ac_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z E F a : Term n) :
    Formula.satisfies ρ (ac_step_m B R z E F a) ↔
      Ac_step_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (E.eval ρ) (F.eval ρ) (a.eval ρ) := by
  simp only [ac_step_m,Ac_step_d,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff,Formula.satisfies_exists_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    ac_pick_sat_l hE,Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem ac_pick_unique_l {B R z E F a b : M.Domain} (fn : M.IsSetFunction I E)
    (ha : Ac_pick_d B R z E F a) (hb : Ac_pick_d B R z E F b) : a = b := by
  obtain ⟨i,hi,ia,_⟩ := ha
  obtain ⟨j,hj,jb,_⟩ := hb
  have eq := hZF.1.eq_of_same_members i j (fun k => (hi k).trans (hj k).symm)
  subst j
  exact fn.2 i a b ia jb

/-- 只给定实际内部枚举时，ZF 已足以完成贪心反链构造。 -/
theorem antichain_enum_l {B R z D α E : M.Domain} (O : Cond_order_d M B R z)
    (hα : M.IsOrdinal α) (fn : M.IsSetFunctionFromTo I E α D) (onto : M.IsSetSurjectiveOnto I E α D) :
    ∃ A, M.MemberSubset A D ∧ Antichain_d M B R z A ∧
      ∀ q, M.mem q D → M.mem q B → q ≠ z → ∃ a, M.mem a A ∧ Cmp_d M B R z q a := by
  classical
  let ρ : Env M 4 := ⟨fun i => [B,R,z,E].get i,fun _ => z⟩
  let φ : BinarySchema 4 := {
    body := ac_step_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 1) .newest }
  have sat f a : φ.denote ρ f a ↔ Ac_step_d B R z E f a := ac_step_sat_l hZF.1 ..
  have functional : M.IsClassFunctionOnTransfiniteSequences I (φ.denote ρ) := by
    intro f _
    by_cases has : ∃ a, Ac_pick_d B R z E f a
    · obtain ⟨a,ha⟩ := has
      refine ⟨a,(sat f a).mpr (Or.inl ha),fun b hb => ?_⟩
      exact ((sat f b).mp hb).elim (fun hb => ac_pick_unique_l hZF fn.1 hb ha)
        (fun hb => (hb.1 ⟨a,ha⟩).elim)
    · exact ⟨z,(sat f z).mpr (Or.inr ⟨has,rfl⟩),fun b hb => ((sat f b).mp hb).elim
        (fun hb => (has ⟨b,hb⟩).elim) And.right⟩
  obtain ⟨F,rec⟩ := ZF.recursiveSequence_exists hZF I ρ φ functional hα
  have step i a (ia : Entry_d M i a F) : ∃ f, M.IsRestrictionOf I f F i ∧ Ac_step_d B R z E f a := by
    obtain ⟨f,cut,h⟩ := rec.2 i ((rec.1.2.2 i).mpr ⟨a,ia⟩) a ia
    exact ⟨f,cut,(sat f a).mp h⟩
  have chosen i a (ia : Entry_d M i a F) (nz : a ≠ z) : ∃ f,
      M.IsRestrictionOf I f F i ∧ Ac_pick_d B R z E f a := by
    obtain ⟨f,cut,h⟩ := step i a ia
    exact ⟨f,cut,h.elim id (fun h => (nz h.2).elim)⟩
  have bound i a (ia : Entry_d M i a F) (nz : a ≠ z) : M.mem a D ∧ M.mem a B := by
    obtain ⟨_,_,_,_,ja,ha,_⟩ := chosen i a ia nz
    exact ⟨fn.output_mem_of_pairMember ja,ha⟩
  let η : Env M 2 := ⟨Fin.cases F (fun _ => z),fun _ => z⟩
  let ψ : UnarySchema 2 := { body := set[3] ⟪⌜(.newest : Term 3)⌝ₛ ≠ ⌜(.bound 2 : Term 3)⌝ₛ ∧
    (∃ i, ⌜entry_m⌝ₚ(i,⌜(.newest : Term 3)⌝ₛ,⌜(.bound 1 : Term 3)⌝ₛ))⟫ }
  obtain ⟨A,members⟩ := ZF.separation_exists_d hZF ψ η D
  have member a : M.mem a A ↔ M.mem a D ∧ a ≠ z ∧ ∃ i, Entry_d M i a F := by
    apply (members a).trans (and_congr_right fun _ => ?_)
    simp only [ψ,Formula.satisfies_conj_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_exists_iff,entry_sat_l M hZF.1,
      Definitional.Term.eval_weaken]
    rfl
  have positive a (ha : M.mem a A) : M.mem a B ∧ a ≠ z := by
    obtain ⟨_,nz,i,ia⟩ := (member a).mp ha
    exact ⟨(bound i a ia nz).2,nz⟩
  have incompatible {i j a b} (ia : Entry_d M i a F) (jb : Entry_d M j b F)
      (az : a ≠ z) (bz : b ≠ z) (ij : M.mem i j) : ¬ Cmp_d M B R z b a := by
    obtain ⟨f,cut,_,_,_,_,_,avoid⟩ := chosen j b jb bz
    exact avoid i a ((cut.2 i a).mpr ⟨ij,ia⟩) az
  have antichain : Antichain_d M B R z A := by
    refine ⟨positive,fun a b ha hb compat => ?_⟩
    obtain ⟨_,az,i,ia⟩ := (member a).mp ha
    obtain ⟨_,bz,j,jb⟩ := (member b).mp hb
    rcases hα.wellOrder.linear.compare i ((rec.1.2.2 i).mpr ⟨a,ia⟩) j ((rec.1.2.2 j).mpr ⟨b,jb⟩) with eq | ij | ji
    · have eq := hZF.1.eq_of_same_members i j eq
      subst j
      exact rec.1.2.1.2 i a b ia jb
    · obtain ⟨r,hr,rb⟩ := compat
      exact (incompatible ia jb az bz ij ⟨r,⟨hr.1,hr.2.1,rb⟩,hr.2.2⟩).elim
    · exact (incompatible jb ia bz az ji compat).elim
  refine ⟨A,fun a ha => ((member a).mp ha).1,antichain,fun q hq hqB qz => ?_⟩
  apply Classical.byContradiction
  intro no
  obtain ⟨i,hi,iq⟩ := onto q hq
  obtain ⟨a,ia⟩ := (rec.1.2.2 i).mp hi
  obtain ⟨f,cut,h⟩ := step i a ia
  have ready : Ac_pick_d B R z E f q := by
    refine ⟨i,(rec.1.restriction hi cut).2.2,iq,hqB,qz,fun j r jr rz compat => ?_⟩
    have jrF := ((cut.2 j r).mp jr).2
    exact no ⟨r,(member r).mpr ⟨(bound j r jrF rz).1,rz,j,jrF⟩,compat⟩
  have aq : a = q := h.elim (fun h => ac_pick_unique_l hZF fn.1 h ready) (fun h => (h.1 ⟨q,ready⟩).elim)
  subst a
  exact no ⟨q,(member q).mpr ⟨hq,qz,i,ia⟩,q,below_refl_l O hqB qz,O.refl q hqB⟩

/-- 原选择公理只负责取得内部枚举，极大性来自上面的实际递归。 -/
theorem antichain_subset_l (hZFC : M.Models ZFC) {B R z : M.Domain} (O : Cond_order_d M B R z) (D : M.Domain) :
    ∃ A, M.MemberSubset A D ∧ Antichain_d M B R z A ∧
      ∀ q, M.mem q D → M.mem q B → q ≠ z → ∃ a, M.mem a A ∧ Cmp_d M B R z q a := by
  obtain ⟨α,E,hα,fn,onto⟩ := ZFC.ordinal_enum_l hZFC (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) D
  exact antichain_enum_l (ZFC.models_zf_l hZFC) O hα fn onto

end YesMetaZFC.Model.Forcing.Internal
