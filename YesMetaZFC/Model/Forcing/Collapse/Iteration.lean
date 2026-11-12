import YesMetaZFC.Model.Forcing.Closed.Basic
import YesMetaZFC.SetTheory.Card.CountableUnion
import YesMetaZFC.SetTheory.PartialFunction
import YesMetaZFC.Model.Forcing.Closed.Syntax
import YesMetaZFC.Model.Forcing.TwoStep.Top
import YesMetaZFC.Model.Forcing.Maximum.Bounded
import YesMetaZFC.Model.Forcing.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Check.Omega
import YesMetaZFC.Model.Forcing.Distributive.NoNewReals
import YesMetaZFC.Model.Forcing.Functions.Generic
import YesMetaZFC.Model.Forcing.TwoStep.Closed
import YesMetaZFC.Model.Forcing.Iteration.Closed.Successor
import YesMetaZFC.Model.Forcing.Iteration.Recursion.Rule
import YesMetaZFC.Model.Forcing.Iteration.Closed.Rule
import YesMetaZFC.Model.Forcing.Closed.ProperName
import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Rule
import YesMetaZFC.Model.Forcing.Iteration.Proper.Induction
import YesMetaZFC.Model.Forcing.Iteration.Closed.Extension

/-! # 地模型内部的可数部分函数塌缩

条件是源集 X 到目标集 Y 的可数部分函数，增强关系为函数图的反向包含。
可数性、函数图、条件集以及序关系都在地模型内部定义。递降 ω 链的并给出
实际下界；此闭性仅量化模型内的序列，不能用于任意外部可数链。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Coll_d (ω X Y p : M.Domain) : Prop := M.IsSetFunction I p ∧
  (∀ x y, M.PairMember I x y p → M.mem x X ∧ M.mem y Y) ∧ M.CardinalLessOrEqual I p ω

def coll_m (𝒞 : OrderedPairConvention) {n} (ω X Y p : Term n) : Formula 1 n :=
  .conj (Formula.isFunction 𝒞 p) (.conj (.forallE (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest p.weaken.weaken)
      (.conj (.mem (.bound 1) X.weaken.weaken) (.mem .newest Y.weaken.weaken)))))
    (Formula.cardinalLessOrEqual 𝒞 p ω))
derive_free_closed coll_m

theorem coll_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω X Y p : Term n) :
    Formula.satisfies ρ (coll_m 𝒞 ω X Y p) ↔ Coll_d I (ω.eval ρ) (X.eval ρ) (Y.eval ρ) (p.eval ρ) := by
  simp only [coll_m, Coll_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_cardinalLessOrEqual_iff I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push,
    Term.eval_bound_zero_push]

theorem coll_set_l (hZF : M.Models ZF) (ω X Y : M.Domain) : ∃ B, ∀ p, M.mem p B ↔ Coll_d I ω X Y p := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I X Y
  obtain ⟨K, hK⟩ := ZF.exists_powerSet hZF P
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y
  let φ : UnarySchema 3 := { body := coll_m 𝒞 (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF φ ρ K
  have hφ p : φ.denote ρ p ↔ Coll_d I ω X Y p :=
    coll_sat_l I hZF.1 (ρ.push p) (.bound 3) (.bound 2) (.bound 1) .newest
  refine ⟨B, fun p => (hB p).trans ?_⟩
  change (M.mem p K ∧ φ.denote ρ p) ↔ _
  rw [hφ]
  refine ⟨And.right, fun hp => ⟨(hK p).mpr ?_, hp⟩⟩
  intro q hq
  obtain ⟨x, y, hcode⟩ := hp.1.1 q hq
  have hxy := hp.2.1 x y ⟨q, hcode, hq⟩
  exact (hP q).mpr ⟨x, hxy.1, y, hxy.2, hcode⟩

theorem coll_empty_l {ω X Y e} (he : ∀ x, ¬ M.mem x e) : Coll_d I ω X Y e := by
  have hseq := SetTheory.Structure.IsSequenceOfLength.empty I he
  refine ⟨hseq.2.1, fun x y ⟨p, _, hp⟩ => False.elim (he p hp), e,
    ⟨hseq.2.1, hseq.2.2, fun x hx => False.elim (he x hx)⟩, ?_⟩
  exact fun x y z ⟨p, _, hp⟩ _ => False.elim (he p hp)

/-- 模型内 ω 链的并仍是可数部分函数。 -/
theorem coll_union_l (hZFC : M.Models ZFC) {ω X Y B f} (hω : M.IsOmega ω)
    (hB : ∀ p, M.mem p B ↔ Coll_d I ω X Y p)
    (hf : M.IsSetFunctionFromTo I f ω B)
    (hd : ∀ i j p q, M.mem i j → M.PairMember I i p f → M.PairMember I j q f → M.MemberSubset p q) :
    ∃ q, M.mem q B ∧ ∀ i p, M.PairMember I i p f → M.MemberSubset p q := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨A, hA⟩ := ZF.exists_range_of_setFunction hZF I hf.1 hf.2.1
  obtain ⟨q, hq⟩ := KP.exists_union (ZF.modelsKP hZF) A
  have ha {p} (hp : M.mem p A) : Coll_d I ω X Y p := by
    obtain ⟨i, hi⟩ := (hA p).mp hp
    exact (hB p).mp (hf.output_mem_of_pairMember hi)
  have hs {i p} (hp : M.PairMember I i p f) : M.MemberSubset p q :=
    fun x hx => (hq x).mpr ⟨p, (hA p).mpr ⟨i, hp⟩, hx⟩
  have hcA : M.CardinalLessOrEqual I A ω := ZFC.surjection_bound_l I hZFC
    ⟨hf.1, hf.2.1, fun i hi => by
      obtain ⟨p, _, hp⟩ := hf.2.2 i hi
      exact ⟨p, (hA p).mpr ⟨i, hp⟩, hp⟩⟩
    (fun p hp => by
      obtain ⟨i, hi⟩ := (hA p).mp hp
      exact ⟨i, hf.input_mem_of_pairMember hi, hi⟩)
  have hc := ZFC.countable_union_l I hZFC hω hcA hq (fun _ hp => (ha hp).2.2)
  refine ⟨q, (hB q).mpr ⟨⟨?_, ?_⟩, ?_, hc⟩, fun _ _ hp => hs hp⟩
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := (hq x).mp hx
    exact (ha hp).1.1 x hxp
  · rintro x y z ⟨v, hv, hvq⟩ ⟨w, hw, hwq⟩
    obtain ⟨p, hp, hvp⟩ := (hq v).mp hvq
    obtain ⟨r, hr, hwr⟩ := (hq w).mp hwq
    obtain ⟨i, hi⟩ := (hA p).mp hp
    obtain ⟨j, hj⟩ := (hA r).mp hr
    rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i (hf.input_mem_of_pairMember hi)
        j (hf.input_mem_of_pairMember hj) with he | hij | hji
    · have he := hZF.1.eq_of_same_members i j he
      subst j
      have he := hf.1.2 i p r hi hj
      subst r
      exact (ha hp).1.2 x y z ⟨v, hv, hvp⟩ ⟨w, hw, hwr⟩
    · exact (ha hr).1.2 x y z ⟨v, hv, hd i j p r hij hi hj v hvp⟩ ⟨w, hw, hwr⟩
    · exact (ha hp).1.2 x y z ⟨v, hv, hvp⟩ ⟨w, hw, hd j i r p hji hj hi w hwr⟩
  · rintro x y ⟨v, hv, hvq⟩
    obtain ⟨p, hp, hvp⟩ := (hq v).mp hvq
    exact (ha hp).2.1 x y ⟨v, hv, hvp⟩

/-- 给定尚未使用的坐标，可以指定任意目标值并保持条件性。 -/
theorem coll_extend_l (hZF : M.Models ZF) {ω X Y p x y} (hω : M.IsOmega ω)
    (hp : Coll_d I ω X Y p) (hx : M.mem x X) (hy : M.mem y Y)
    (hn : ¬ ∃ z, M.PairMember I x z p) :
    ∃ q, Coll_d I ω X Y q ∧ M.MemberSubset p q ∧ M.PairMember I x y q := by
  obtain ⟨q, v, _, hq, hqf, hxy⟩ := ZF.pfn_insert_l I hZF ⟨hp.1, hp.2.1⟩ hx hy hn
  exact ⟨q, ⟨hqf.1, hqf.2, ZF.countable_insert_l I hZF hω hp.2.2 hq⟩,
    fun w hw => (hq w).mpr (Or.inl hw), hxy⟩

/-- 不可数源集中总有一个尚未使用的坐标。 -/
theorem coll_fresh_l (hZF : M.Models ZF) {ω X Y p} (hp : Coll_d I ω X Y p)
    (hX : ¬ M.CardinalLessOrEqual I X ω) : ∃ x, M.mem x X ∧ ¬ ∃ y, M.PairMember I x y p := by
  classical
  apply Classical.byContradiction
  intro hn
  have ht x (hx : M.mem x X) : ∃ y, M.PairMember I x y p := by
    apply Classical.byContradiction
    exact fun h => hn ⟨x, hx, h⟩
  let ρ : Env M 1 := ⟨fun _ => p, fun _ => p⟩
  let φ : BinarySchema 1 := {
    body := .conj (.mem .newest (.bound 2)) (.existsE (𝒞.code (.bound 1) (.bound 2) .newest)) }
  have hφ x q : φ.denote ρ x q ↔ M.mem q p ∧ ∃ y, I.Codes q x y := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, I.satisfies_code_iff]
    rfl
  obtain ⟨F, hF⟩ := ZF.exists_setInjectionFromTo_of_denote hZF I φ ρ (source := X) (target := p) (by
    intro x hx
    obtain ⟨y, q, hq, hqp⟩ := ht x hx
    exact ⟨q, (hφ x q).mpr ⟨hqp, y, hq⟩⟩) (by
    intro x _ q r hq hr
    obtain ⟨hqp, y, hq⟩ := (hφ x q).mp hq
    obtain ⟨hrp, z, hr⟩ := (hφ x r).mp hr
    have he := hp.1.2 x y z ⟨q, hq, hqp⟩ ⟨r, hr, hrp⟩
    subst z
    exact I.unique hq hr) (fun x q _ hq => ((hφ x q).mp hq).1) (by
    intro x y q _ _ hx hy
    obtain ⟨_, a, hx⟩ := (hφ x q).mp hx
    obtain ⟨_, b, hy⟩ := (hφ y q).mp hy
    exact (I.injective hx hy).1)
  obtain ⟨G, hG⟩ := hp.2.2
  exact hX (ZF.exists_compositionInjection hZF I hF hG)

variable (M : SetTheory.Structure.{u})

/-- 实际条件集和反向包含序；B 本身由基础公理保证不在 B 中，作为排除值。 -/
theorem collapse_order_l (hZF : M.Models ZF) (ω X Y : M.Domain) : ∃ B R,
    (∀ p, M.mem p B ↔ Coll_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω X Y p) ∧
    (∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p) ∧
    Cond_order_d M B R B := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨B, hB⟩ := coll_set_l I hZF ω X Y
  obtain ⟨R, hR, hO, _⟩ := subset_order_l M hZF B
  exact ⟨B, R, hB, hR, hO⟩

/-- 可数部分函数塌缩具有已实现的模型内部可数闭性。 -/
theorem collapse_closed_l (hZFC : M.Models ZFC) {ω} (hω : M.IsOmega ω) (X Y : M.Domain) : ∃ B R,
    (∀ p, M.mem p B ↔ Coll_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω X Y p) ∧
    (∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p) ∧
    Cond_order_d M B R B ∧ Closed_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B R B ω := by
  let hZF := ZFC.models_zf_l hZFC
  let J := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨B, R, hB, hR, O⟩ := collapse_order_l M hZF ω X Y
  refine ⟨B, R, hB, hR, O, fun f hf => ?_⟩
  obtain ⟨q, hq, hqs⟩ := coll_union_l J hZFC hω hB hf.1 (fun i j p q hij hip hjq =>
    ((hR q p).mp (chain_lower_l O hZF hω hf i j p q hij hip hjq)).2.2)
  refine ⟨q, hq, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hq), fun i p hip => ?_⟩
  exact (hR q p).mpr ⟨hq, hf.1.output_mem_of_pairMember hip, hqs i p hip⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 可数部分函数偏序的原公式规格

条件集和完整反向包含关系由参数唯一确定；只在证明可数闭性时使用 ZFC。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Coll_spec_d (I : kpair_convention_l.Interpretation M) (ω X Y Q T : M.Domain) : Prop :=
  (∀ p, M.mem p Q ↔ Coll_d I ω X Y p) ∧ (∀ v, M.mem v T → ∃ p q, KPair_d M v p q) ∧
    ∀ p q, Entry_d M p q T ↔ M.mem p Q ∧ M.mem q Q ∧ M.MemberSubset q p

def coll_spec_m {n} (ω X Y Q T : Term n) : Formula 1 n :=
  .conj (.forallE (.iff (.mem .newest Q.weaken)
    (coll_m kpair_convention_l ω.weaken X.weaken Y.weaken .newest)))
    (.conj (Formula.isRelation kpair_convention_l T) (.forallE (.forallE
      (.iff (entry_m (.bound 1) .newest T.weaken.weaken)
        (.conj (.mem (.bound 1) Q.weaken.weaken)
          (.conj (.mem .newest Q.weaken.weaken) (Formula.subset .newest (.bound 1))))))))
derive_free_closed coll_spec_m

theorem coll_spec_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (ω X Y Q T : Term n) : Formula.satisfies ρ (coll_spec_m ω X Y Q T) ↔
      Coll_spec_d I (ω.eval ρ) (X.eval ρ) (Y.eval ρ) (Q.eval ρ) (T.eval ρ) := by
  simp only [coll_spec_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, coll_sat_l I hE]
  simp only [Coll_spec_d, Formula.satisfies_mem_iff, Formula.isRelation,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, kpair_sat_l M hE,
    kpair_convention_l, entry_sat_l M hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

theorem coll_spec_exists_l (hZF : M.Models ZF) (ω X Y : M.Domain) : ∃ Q T,
    Coll_spec_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω X Y Q T := by
  obtain ⟨Q, hQ⟩ := coll_set_l (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) hZF ω X Y
  obtain ⟨T, hT, _, hGraph⟩ := subset_order_l M hZF Q
  exact ⟨Q, T, hQ, hGraph, hT⟩

theorem coll_spec_unique_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {ω X Y Q T Q' T'}
    (h : Coll_spec_d I ω X Y Q T) (h' : Coll_spec_d I ω X Y Q' T') : Q = Q' ∧ T = T' := by
  have he := hE.eq_of_same_members Q Q' (fun p => (h.1 p).trans (h'.1 p).symm)
  subst Q'
  exact ⟨rfl, entry_ext_l M hE h.2.1 h'.2.1 (fun p q => (h.2.2 p q).trans (h'.2.2 p q).symm)⟩

theorem coll_spec_top_l (I : kpair_convention_l.Interpretation M) {ω X Y Q T o}
    (h : Coll_spec_d I ω X Y Q T) (ho : ∀ x, ¬ M.mem x o) :
    Preord_d M Q T ∧ M.mem o Q ∧ ∀ p, M.mem p Q → Entry_d M p o T := by
  have hoQ := (h.1 o).mpr (coll_empty_l I ho)
  exact ⟨⟨fun p hp => (h.2.2 p p).mpr ⟨hp, hp, fun _ h => h⟩,
    fun p q r hp _ hr hpq hqr => (h.2.2 p r).mpr
      ⟨hp, hr, fun x hx => ((h.2.2 p q).mp hpq).2.2 x (((h.2.2 q r).mp hqr).2.2 x hx)⟩⟩,
    hoQ, fun p hp => (h.2.2 p o).mpr ⟨hp, hoQ, fun x hx => (ho x hx).elim⟩⟩

theorem coll_spec_top_unique_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {ω X Y Q T t u}
    (h : Coll_spec_d I ω X Y Q T)
    (ht : M.mem t Q ∧ ∀ p, M.mem p Q → Entry_d M p t T)
    (hu : M.mem u Q ∧ ∀ p, M.mem p Q → Entry_d M p u T) : t = u :=
  hE.eq_of_same_members t u (fun x =>
    ⟨((h.2.2 u t).mp (ht.2 u hu.1)).2.2 x, ((h.2.2 t u).mp (hu.2 t ht.1)).2.2 x⟩)

theorem coll_spec_closed_l (hZFC : M.Models ZFC) {ω X Y Q T} (hω : M.IsOmega ω)
    (h : Coll_spec_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC))))
      ω X Y Q T) : Closed_d (kpair_interpretation_l M hZFC.1
        (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) Q T Q ω := by
  have hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨o, ho⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hP := (coll_spec_top_l I h ho).1
  have O : Cond_order_d M Q T Q := ⟨hP.1, hP.2,
    fun p _ hp => (KP.mem_irrefl_d (ZF.modelsKP hZF) Q ((h.2.2 p Q).mp hp).2.1).elim⟩
  intro f hf
  obtain ⟨q, hq, hqs⟩ := coll_union_l I hZFC hω h.1 hf.1 (fun i j p q hij hip hjq =>
    ((h.2.2 q p).mp (chain_lower_l O hZF hω hf i j p q hij hip hjq)).2.2)
  exact ⟨q, hq, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) Q (he ▸ hq),
    fun i p hip => (h.2.2 q p).mpr ⟨hq, hf.1.output_mem_of_pairMember hip, hqs i p hip⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 可数部分函数后继的实际名称

任意大小界、源集和目标集名称决定条件集、关系和顶名称。三次最大值选择均返回
规范名称；原 ZFC 的实际塌缩构造同时证明其规格、预序、顶及条件式可数闭性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

def coll_closed_body_m : Formula 1 3 :=
  .imp (Formula.isOmega (.bound 2)) (closed_m (.bound 1) .newest (.bound 1) (.bound 2))

def coll_names_body_m : Formula 1 6 :=
  .conj (coll_spec_m (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 2))
    (.conj ((preord_m .newest (.bound 1) : Formula 1 2).bind (Fin.cases (.bound 1) (fun _ => .bound 2)))
      (.conj ((top_m (.bound 1) (.bound 2) .newest : Formula 1 3).bind (fun i => .bound i.castSucc.castSucc.castSucc))
        (coll_closed_body_m.bind (Fin.cases (.bound 2) (Fin.cases (.bound 1) (fun _ => .bound 5))))))

@[simp] theorem coll_closed_body_closed_l : coll_closed_body_m.FreeClosed := by
  simp -implicitDefEqProofs [coll_closed_body_m, Definitional.Formula.FreeClosed]

@[simp] theorem coll_names_body_closed_l : coll_names_body_m.FreeClosed := by
  simp only [coll_names_body_m, Definitional.Formula.FreeClosed]
  refine ⟨coll_spec_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl, ?_, ?_, ?_⟩
  · exact (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases rfl (fun _ => rfl)) _).mpr
      (preord_m_freeClosed _ _ rfl rfl)
  · exact (Definitional.Formula.freeClosed_bind_iff_of_closed _ (fun _ => rfl) _).mpr
      (top_m_freeClosed _ _ _ rfl rfl rfl)
  · exact (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) _).mpr
      coll_closed_body_closed_l

def coll_names_env_l (w X Y A T t : M.Domain) : Env M 6 :=
  (((((⟨fun _ => w, fun _ => w⟩ : Env M 1).push X).push Y).push T).push A).push t

def Coll_names_d (I : kpair_convention_l.Interpretation M) (B R z w X Y A T t : M.Domain) : Prop :=
  (Name_d M B A ∧ Name_d M B T ∧ Name_d M B t) ∧
    (∀ s, s = A ∨ s = T ∨ s = t → Norm_name_d M I B R z s s) ∧
    ∀ p, M.mem p B → p ≠ z → Forces_d M B R z coll_names_body_m (coll_names_env_l w X Y A T t) p

theorem collapse_names_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {w X Y}
    (hw : Name_d M B w) (hX : Name_d M B X) (hY : Name_d M B Y) : ∃ A T t,
      Coll_names_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC))))
        B R z w X Y A T t := by
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push X).push Y
  let φ : UnarySchema 3 := ⟨.existsE (.existsE coll_names_body_m),
    by simpa only [Definitional.Formula.FreeClosed] using coll_names_body_closed_l⟩
  let ψ : UnarySchema 4 := ⟨.existsE coll_names_body_m,
    by simpa only [Definitional.Formula.FreeClosed] using coll_names_body_closed_l⟩
  let θ : UnarySchema 5 := ⟨coll_names_body_m, coll_names_body_closed_l⟩
  have hρ : ∀ i, Name_d M B (ρ.bound i) := Fin.cases hY (Fin.cases hX (fun _ => hw))
  have valid (N : SetTheory.Structure.{u}) (hN : N.Models ZFC) (η : Env N 3) :
      Formula.satisfies η (.existsE φ.body) := by
    have hZF := ZFC.models_zf_l hN
    let I := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hZF))
    obtain ⟨Q, D, h⟩ := coll_spec_exists_l hZF (η.bound 2) (η.bound 1) (η.bound 0)
    obtain ⟨o, ho⟩ := KP.exists_empty (ZF.modelsKP hZF)
    obtain ⟨hp, htop⟩ := coll_spec_top_l I h ho
    simp only [φ, Formula.satisfies_exists_iff]
    refine ⟨D, Q, o, ?_⟩
    simp only [coll_names_body_m, Formula.satisfies_conj_iff, Formula.satisfies_bind]
    refine ⟨(coll_spec_sat_l I hN.1 _ _ _ _ _ _).mpr h, (preord_sat_l hN.1 _ _ _).mpr hp,
      (top_sat_l hN.1 _ _ _ _).mpr htop, ?_⟩
    simp only [coll_closed_body_m, Formula.satisfies_imp_iff, Formula.satisfies_isOmega_iff,
      closed_sat_l I hN.1]
    exact fun hω => coll_spec_closed_l hN hω h
  obtain ⟨T, hT, hTN, ht⟩ := maximum_l O hZFC φ ρ hρ
  have hTφ p (hp : M.mem p B) (hz : p ≠ z) := (ht p hp hz).mp
    (forces_valid_l O hZFC (.existsE φ.body)
      (by simpa only [φ, Definitional.Formula.FreeClosed] using coll_names_body_closed_l) valid ρ hρ hp hz)
  obtain ⟨A, hA, hAN, ha⟩ := maximum_l O hZFC ψ (ρ.push T) (Fin.cases hT hρ)
  have hAφ p hp hz := (ha p hp hz).mp (hTφ p hp hz)
  obtain ⟨t, ht, htN, hmax⟩ := maximum_l O hZFC θ ((ρ.push T).push A) (Fin.cases hA (Fin.cases hT hρ))
  exact ⟨A, T, t, ⟨hA, hT, ht⟩, fun s hs => hs.elim (fun he => he.symm ▸ hAN)
    (fun hs => hs.elim (fun he => he.symm ▸ hTN) (fun he => he.symm ▸ htN)),
    fun p hp hz => (hmax p hp hz).mp (hAφ p hp hz)⟩

/-- 当大小界是旧 ω 的规范名称时，预序、顶和可数闭性均为实际力迫结论。 -/
theorem collapse_names_closed_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {b ω w X Y A T t p}
    (hω : M.IsOmega ω) (hb : M.mem b B) (hw : Check_d M b ω w) (hp : Below_d M B R z p b)
    (h : Coll_names_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC))))
      B R z w X Y A T t) :
    Forces_d M B R z (preord_m .newest (.bound 1)) (ord_env_l M A T) p ∧
    Forces_d M B R z (top_m (.bound 1) (.bound 2) .newest) (top_env_l A T t) p ∧
    Forces_d M B R z (closed_m (.bound 1) .newest (.bound 1) (.bound 2))
      (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T) p := by
  have hZF := ZFC.models_zf_l hZFC
  have hf := ((forces_conj_l _ _ _ p).mp (h.2.2 p hp.1 hp.2.1)).2
  obtain ⟨hP, ht, hc⟩ := (forces_conj_l _ _ _ p).mp hf |>.imp_right fun h => (forces_conj_l _ _ _ p).mp h
  have hP := (forces_bind_l hZF.1 _ _ _ p).mp hP
  have ht := (forces_bind_l hZF.1 _ _ _ p).mp ht
  have hc := (forces_bind_l hZF.1 _ _ _ p).mp hc
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T
  have hc : Forces_d M B R z coll_closed_body_m ρ p :=
    (forces_env_l hZF.1 _ coll_closed_body_closed_l _ ρ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) p).mp hc
  have hwf := check_omega_force_l O hZF hω hb hw hp
  have hwf : Forces_d M B R z (Formula.isOmega (.bound 2)) ρ p := by
    have hbind : (Formula.isOmega (.newest : Term 1)).bind (fun _ : Fin 1 => (.bound 2 : Term 3)) =
        Formula.isOmega (.bound 2) := by
      simp [Formula.isOmega, Formula.isInductive, Formula.isEmpty, Formula.isSuccessor, Formula.forallMem,
        Formula.extensionalEq, Formula.subset, Definitional.Formula.bind, Definitional.Term.bind,
        Definitional.Term.liftSubstitution, Definitional.Term.newest, Definitional.Term.weaken,
        Definitional.Term.rename, Definitional.TermVector.bind, Formula.pairArguments,
        fin_cases]
    have hh := (forces_bind_l hZF.1 (Formula.isOmega .newest) (fun _ : Fin 1 => (.bound 2 : Term 3)) ρ p).mpr
      ((forces_env_l hZF.1 (Formula.isOmega .newest) (Formula.isOmega_freeClosed _ rfl)
        (⟨fun _ => w, fun _ => w⟩ : Env M 1)
        (Definitional.Env.substitute ρ (fun _ : Fin 1 => (.bound 2 : Term 3))) (fun _ => rfl) p).mp hwf)
    exact hbind ▸ hh
  have hn : ∀ a : Term 3, Name_d M B (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact check_name_l M (check_range_l M hZF) hb hw
    | bound i => exact Fin.cases h.1.2.1 (Fin.cases h.1.1 (fun _ => check_name_l M (check_range_l M hZF) hb hw)) i
  exact ⟨(forces_env_l hZF.1 _ (preord_m_freeClosed _ _ rfl rfl) _ _ (Fin.cases rfl (fun _ => rfl)) p).mp hP,
    (forces_env_l hZF.1 _ (top_m_freeClosed _ _ _ rfl rfl rfl) _ _
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) p).mp ht,
    forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hn).1 (forces_regular_l O hZF _ ρ hn) hp.1 hp.2.1 hc hwf⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 塌缩后继名称的字面唯一性

两份完整规格在任意泛型中给出同一条件集、关系和顶。原 ZF 有效性将其转成
全局等号力迫；规范名称固定点随后给出字面相等，供确定超限递归使用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem collapse_names_unique_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {w X Y A T t A' T' t'}
    (hw : Name_d M B w) (hX : Name_d M B X) (hY : Name_d M B Y)
    (h : Coll_names_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z w X Y A T t)
    (h' : Coll_names_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z w X Y A' T' t') :
    A = A' ∧ T = T' ∧ t = t' := by
  let el : Fin 6 → Term 9 := Fin.cases (.bound 3) (Fin.cases (.bound 4) (Fin.cases (.bound 5)
    (Fin.cases (.bound 6) (Fin.cases (.bound 7) (fun _ => .bound 8)))))
  let er : Fin 6 → Term 9 := Fin.cases .newest (Fin.cases (.bound 1) (Fin.cases (.bound 2)
    (Fin.cases (.bound 6) (Fin.cases (.bound 7) (fun _ => .bound 8)))))
  have hel : ∀ i, (el i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  have her : ∀ i, (er i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  let β : Formula 1 9 := .conj (Formula.extensionalEq (.bound 4) (.bound 1))
    (.conj (Formula.extensionalEq (.bound 5) (.bound 2)) (Formula.extensionalEq (.bound 3) .newest))
  let φ : Formula 1 9 := .imp (coll_names_body_m.bind el) (.imp (coll_names_body_m.bind er) β)
  have hβ : β.FreeClosed := by simp -implicitDefEqProofs [β, Definitional.Formula.FreeClosed]
  have hφ : φ.FreeClosed := by
    simp only [φ, Definitional.Formula.FreeClosed]
    exact ⟨(Definitional.Formula.freeClosed_bind_iff_of_closed _ hel _).mpr coll_names_body_closed_l,
      (Definitional.Formula.freeClosed_bind_iff_of_closed _ her _).mpr coll_names_body_closed_l, hβ⟩
  have valid (N : SetTheory.Structure.{u}) (hN : N.Models ZF) (η : Env N 9) : Formula.satisfies η φ := by
    simp only [φ, Formula.satisfies_imp_iff, Formula.satisfies_bind]
    intro hl hr
    simp only [coll_names_body_m, Formula.satisfies_conj_iff, Formula.satisfies_bind] at hl hr
    let J := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))
    have hs := (coll_spec_sat_l J hN.1 _ _ _ _ _ _).mp hl.1
    have hs' := (coll_spec_sat_l J hN.1 _ _ _ _ _ _).mp hr.1
    change Coll_spec_d J (η.bound 8) (η.bound 7) (η.bound 6) (η.bound 4) (η.bound 5) at hs
    change Coll_spec_d J (η.bound 8) (η.bound 7) (η.bound 6) (η.bound 1) (η.bound 2) at hs'
    obtain ⟨hQ, hT⟩ := coll_spec_unique_l J hN.1 hs hs'
    have ht := (top_sat_l hN.1 _ _ _ _).mp hl.2.2.1
    have ht' := (top_sat_l hN.1 _ _ _ _).mp hr.2.2.1
    change (N.mem (η.bound 3) (η.bound 4) ∧ ∀ p, N.mem p (η.bound 4) → Entry_d N p (η.bound 3) (η.bound 5)) at ht
    change (N.mem (η.bound 0) (η.bound 1) ∧ ∀ p, N.mem p (η.bound 1) → Entry_d N p (η.bound 0) (η.bound 2)) at ht'
    rw [← hQ, ← hT] at ht'
    have ho := coll_spec_top_unique_l J hN.1 hs ht ht'
    simp only [β, Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hN.1]
    exact ⟨hQ, hT, ho⟩
  let ρ : Env M 9 := (((coll_names_env_l w X Y A T t).push T').push A').push t'
  have hn : ∀ s : Term 9, Name_d M B (s.eval ρ) := by
    intro s
    cases s with
    | free _ => exact hw
    | bound i => exact Fin.cases h'.1.2.2 (Fin.cases h'.1.1 (Fin.cases h'.1.2.1
        (Fin.cases h.1.2.2 (Fin.cases h.1.1 (Fin.cases h.1.2.1 (Fin.cases hY (Fin.cases hX (fun _ => hw)))))))) i
  have both p (hp : M.mem p B) (hz : p ≠ z) :
      Eq_force_d M B R z p A A' ∧ Eq_force_d M B R z p T T' ∧ Eq_force_d M B R z p t t' := by
    have hleft := (forces_bind_l hZF.1 coll_names_body_m el ρ p).mpr
      ((forces_env_l hZF.1 _ coll_names_body_closed_l (coll_names_env_l w X Y A T t) (Definitional.Env.substitute ρ el)
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))) p).mp (h.2.2 p hp hz))
    have hright := (forces_bind_l hZF.1 coll_names_body_m er ρ p).mpr
      ((forces_env_l hZF.1 _ coll_names_body_closed_l (coll_names_env_l w X Y A' T' t') (Definitional.Env.substitute ρ er)
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))) p).mp (h'.2.2 p hp hz))
    have hi := forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hn).1 (forces_regular_l O hZF _ ρ hn) hp hz
      (forces_zf_valid_l O hZF φ hφ valid ρ (fun i => hn (.bound i)) hp hz) hleft
    have he := forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hn).1 (forces_regular_l O hZF β ρ hn) hp hz hi hright
    obtain ⟨hA, hT, ht⟩ := (forces_conj_l _ _ _ p).mp he |>.imp_right fun h => (forces_conj_l _ _ _ p).mp h
    exact ⟨(code_eq_l M hZF.1 B R z _ _ ρ p).mp hA, (code_eq_l M hZF.1 B R z _ _ ρ p).mp hT,
      (code_eq_l M hZF.1 B R z _ _ ρ p).mp ht⟩
  exact ⟨norm_name_congr_l O hZF h.1.1 h'.1.1 (fun p hp hz => (both p hp hz).1)
      (h.2.1 A (Or.inl rfl)) (h'.2.1 A' (Or.inl rfl)),
    norm_name_congr_l O hZF h.1.2.1 h'.1.2.1 (fun p hp hz => (both p hp hz).2.1)
      (h.2.1 T (Or.inr (Or.inl rfl))) (h'.2.1 T' (Or.inr (Or.inl rfl))),
    norm_name_congr_l O hZF h.1.2.2 h'.1.2.2 (fun p hp hz => (both p hp hz).2.2)
      (h.2.1 t (Or.inr (Or.inr rfl))) (h'.2.1 t' (Or.inr (Or.inr rfl)))⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范塌缩名称三元组的原公式

公式保留全部名称性、规范固定点与全局规格力迫，确定规则直接使用该已实现关系。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def coll_names_m {n} (B R z w X Y A T t : Term n) : Formula 1 n :=
  .conj (.conj (name_m B A) (.conj (name_m B T) (name_m B t)))
    (.conj (.conj (norm_name_m B R z A A) (.conj (norm_name_m B R z T T) (norm_name_m B R z t t)))
      (force_all_m coll_names_body_m (Fin.cases t (Fin.cases A (Fin.cases T (Fin.cases Y (Fin.cases X (fun _ => w)))))) B R z))

@[simp] theorem coll_names_closed_l {n} (B R z w X Y A T t : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = []) (hw : w.freeSupport = [])
    (hX : X.freeSupport = []) (hY : Y.freeSupport = []) (hA : A.freeSupport = []) (hT : T.freeSupport = []) (ht : t.freeSupport = []) :
    (coll_names_m B R z w X Y A T t).FreeClosed := by
  simp only [coll_names_m, Definitional.Formula.FreeClosed]
  exact ⟨⟨name_m_freeClosed _ _ hB hA, name_m_freeClosed _ _ hB hT, name_m_freeClosed _ _ hB ht⟩,
    ⟨norm_name_closed_l _ _ _ _ _ hB hR hz hA hA, norm_name_closed_l _ _ _ _ _ hB hR hz hT hT,
      norm_name_closed_l _ _ _ _ _ hB hR hz ht ht⟩,
    force_all_closed_l _ _ _ _ _ coll_names_body_closed_l
      (Fin.cases ht (Fin.cases hA (Fin.cases hT (Fin.cases hY (Fin.cases hX (fun _ => hw)))))) hB hR hz⟩

theorem coll_names_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (B R z w X Y A T t : Term n) : Formula.satisfies ρ (coll_names_m B R z w X Y A T t) ↔
      Coll_names_d I (B.eval ρ) (R.eval ρ) (z.eval ρ) (w.eval ρ) (X.eval ρ) (Y.eval ρ) (A.eval ρ) (T.eval ρ) (t.eval ρ) := by
  simp only [coll_names_m, Formula.satisfies_conj_iff, name_sat_l M hE, norm_name_sat_l M I hE, force_all_sat_l hE]
  let e : Fin 6 → Term n := Fin.cases t (Fin.cases A (Fin.cases T (Fin.cases Y (Fin.cases X (fun _ => w)))))
  have he p := forces_env_l (B := B.eval ρ) (R := R.eval ρ) (z := z.eval ρ) hE coll_names_body_m coll_names_body_closed_l
    (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M 6)
    (coll_names_env_l (w.eval ρ) (X.eval ρ) (Y.eval ρ) (A.eval ρ) (T.eval ρ) (t.eval ρ))
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))) p
  simp only [e] at he
  simp only [he]
  exact ⟨fun h => ⟨h.1, fun s hs => hs.elim (fun e => e.symm ▸ h.2.1.1)
      (fun hs => hs.elim (fun e => e.symm ▸ h.2.1.2.1) (fun e => e.symm ▸ h.2.1.2.2)), h.2.2⟩,
    fun h => ⟨h.1, ⟨h.2.1 _ (Or.inl rfl), h.2.1 _ (Or.inr (Or.inl rfl)), h.2.1 _ (Or.inr (Or.inr rfl))⟩, h.2.2⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 塌缩泛型函数的内部名称

每个条件中的有序对赋以该条件为权重，得到实际内部关系名称。
指定坐标稠密集保证全定义，指定值稠密集保证满射，滤子的共同加强保证单值。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SmallGraph
universe u
variable {M : SetTheory.Structure.{u}} {B R ω : M.Domain} {U : M.Domain → Prop}

variable (O : Cond_order_d M B R B) (hZFC : M.Models ZFC) (hU : Generic_d M B R B U)
local notation "E" => extension_l M (ZFC.models_zf_l hZFC) B R B U
variable {hEN : Extensional (extension_l M (ZFC.models_zf_l hZFC) B R B U)}
  {hPN : ∀ a b, ∃ p, Pair_d (extension_l M (ZFC.models_zf_l hZFC) B R B U) p a b}
include O hZFC hU hEN hPN

theorem collapse_surjection_l {X Y b} (hω : M.IsOmega ω) (hb : U b)
    (hB : ∀ p, M.mem p B ↔ Coll_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω X Y p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (hX : ¬ M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) X ω) (hY : ∃ y, M.mem y Y)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, (E).mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a t, Check_d M b a t → Qval_d M B R B U t (e a)) :
    ∃ F : (E).Domain, (E).IsSetFunctionFromTo (kpair_interpretation_l E hEN hPN) F (e X) (e Y) ∧
      (E).IsSetSurjectiveOnto (kpair_interpretation_l E hEN hPN) F (e X) (e Y) := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let J := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  have hp {p} (hp : U p) : Coll_d J ω X Y p := (hB p).mp (hU.proper p hp).1
  have hbelow {p q} (hq : Coll_d J ω X Y q) (hpp : M.mem p B) (hs : M.MemberSubset p q) :
      Below_d M B R B q p := by
    have hqB := (hB q).mpr hq
    exact ⟨hqB, fun heq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (heq ▸ hqB), (hR q p).mpr ⟨hqB, hpp, hs⟩⟩
  obtain ⟨p₀, hp₀⟩ := hU.inhabited
  have input a (ha : M.mem a X) : ∃ p, U p ∧ ∃ c, Entry_d M a c p := by
    let φ : UnarySchema 1 := { body := .existsE (entry_m (.bound 2) .newest (.bound 1)) }
    let ρ : Env M 1 := ⟨fun _ => a, fun _ => a⟩
    have hφ p : φ.denote ρ p ↔ ∃ c, Entry_d M a c p := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, entry_sat_l M hZF.1]
      rfl
    apply generic_pick_l hZF hU ⟨1, φ, ρ, hφ⟩ hp₀
    intro p hpp
    by_cases hn : ∃ c, Entry_d M a c p
    · exact ⟨p, below_refl_l O hpp.1 hpp.2.1, hn⟩
    · obtain ⟨c, hc⟩ := hY
      obtain ⟨q, hq, hqp, hac⟩ := coll_extend_l J hZF hω ((hB p).mp hpp.1) ha hc hn
      exact ⟨q, hbelow hq hpp.1 hqp, c, hac⟩
  have output c (hc : M.mem c Y) : ∃ p, U p ∧ ∃ a, Entry_d M a c p := by
    let φ : UnarySchema 1 := { body := .existsE (entry_m .newest (.bound 2) (.bound 1)) }
    let ρ : Env M 1 := ⟨fun _ => c, fun _ => c⟩
    have hφ p : φ.denote ρ p ↔ ∃ a, Entry_d M a c p := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, entry_sat_l M hZF.1]
      rfl
    apply generic_pick_l hZF hU ⟨1, φ, ρ, hφ⟩ hp₀
    intro p hpp
    obtain ⟨a, ha, hn⟩ := coll_fresh_l J hZF ((hB p).mp hpp.1) hX
    obtain ⟨q, hq, hqp, hac⟩ := coll_extend_l J hZF hω ((hB p).mp hpp.1) ha hc hn
    exact ⟨q, hbelow hq hpp.1 hqp, a, hac⟩
  obtain ⟨F, hF, hf⟩ := generic_function_l (hEN := hEN) (hPN := hPN) O hZF hU hb
    (fun hp' => ⟨(hp hp').1, (hp hp').2.1⟩) (fun p q h => ((hR p q).mp h).2.2) input e hi he hv
  refine ⟨F, hF, ?_⟩
  intro y hy
  obtain ⟨c, hc, rfl⟩ := (he Y y).mp hy
  obtain ⟨p, hp', a, hac⟩ := output c hc
  exact ⟨e a, (image_member_l e hi he).mpr ((hp hp').2.1 a c hac).1,
    (hf (e a) (e c)).mpr ⟨p, hp', a, c, hac, rfl, rfl⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 可数闭首阶段后的参数化塌缩

后继的条件域、序关系、顶名称和闭性力迫均实际构造，再调用二步闭性定理。
最后从两组任意地模型集合参数自动装配两个可数部分函数塌缩。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 后继源集、目标集允许任意名称，实际二步偏序自动返回可数闭证书和顶条件。 -/
theorem collapse_two_step_closed_l {B R z b ω X Y} (O : Cond_order_d M B R z)
    (hω : M.IsOmega ω) (hb : M.mem b B) (hz : b ≠ z) (hc : Closed_d I B R z ω)
    (hX : Name_d M B X) (hY : Name_d M B Y) : ∃ w A T t W C S,
      Check_d M b ω w ∧ Coll_names_d I B R z w X Y A T t ∧
      Two_step_d M B R z b A T W C S ∧ Name_pool_d M B A t W ∧
      Cond_order_d M C S C ∧ Closed_d I C S C ω ∧
      ∃ q, KPair_d M q b t ∧ M.mem q C ∧ ∀ r, M.mem r C → Entry_d M r q S := by
  obtain ⟨w, hw, hwN, _⟩ := zf_check_l M hZF hb ω
  obtain ⟨A, T, t, hn⟩ := collapse_names_l O hZFC hwN hX hY
  obtain ⟨hP, ht, hc'⟩ := collapse_names_closed_l O hZFC hω hb hw (below_refl_l O hb hz) hn
  obtain ⟨W, C, S, h, L, hW, htop⟩ := two_step_pointed_l O hZF hn.1.1 hn.1.2.1 hn.1.2.2 hb hz hP ht
  exact ⟨w, A, T, t, W, C, S, hw, hn, h, hW, L, two_step_closed_l O hZFC h hW hn.1.2.1 hP hω hw hc hc', htop⟩

/-- 两组集合参数直接生成可数闭二步塌缩；所有名称与闭性前提由实际构造消去。 -/
theorem collapse_pair_closed_l {ω} (hω : M.IsOmega ω) (X₀ Y₀ X₁ Y₁ : M.Domain) :
    ∃ B R b x y w A T t W C S,
      Coll_spec_d I ω X₀ Y₀ B R ∧ Cond_order_d M B R B ∧ Closed_d I B R B ω ∧
      M.mem b B ∧ Check_d M b X₁ x ∧ Check_d M b Y₁ y ∧ Check_d M b ω w ∧
      Coll_names_d I B R B w x y A T t ∧ Two_step_d M B R B b A T W C S ∧
      Name_pool_d M B A t W ∧ Cond_order_d M C S C ∧ Closed_d I C S C ω ∧
      ∃ q, KPair_d M q b t ∧ M.mem q C ∧ ∀ r, M.mem r C → Entry_d M r q S := by
  obtain ⟨B, R, h⟩ := coll_spec_exists_l hZF ω X₀ Y₀
  obtain ⟨b, hb⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨hP, hbB, _⟩ := coll_spec_top_l I h hb
  have O : Cond_order_d M B R B := ⟨hP.1, hP.2,
    fun p _ hp => (KP.mem_irrefl_d (ZF.modelsKP hZF) B ((h.2.2 p B).mp hp).2.1).elim⟩
  have hc := coll_spec_closed_l hZFC hω h
  obtain ⟨x, hx, hxN, _⟩ := zf_check_l M hZF hbB X₁
  obtain ⟨y, hy, hyN, _⟩ := zf_check_l M hZF hbB Y₁
  obtain ⟨w, A, T, t, W, C, S, hw, hn, hs, hW, L, hcs, htop⟩ :=
    collapse_two_step_closed_l hZFC O hω hbB (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hbB)) hc hxN hyN
  exact ⟨B, R, b, x, y, w, A, T, t, W, C, S, h, O, hc, hbB, hx, hy, hw, hn, hs, hW, L, hcs, htop⟩

/-- 在已有可数闭坐标阶段上实际追加塌缩，保留阶段链接及两种支撑约束。 -/
theorem row_collapse_closed_l {α β B R b ω X Y} (h : Row_stage_d M α B R b)
    (hβ : M.SuccessorOf β α) (hω : M.IsOmega ω) (hc : Closed_d I B R B ω)
    (hX : Name_d M B X) (hY : Name_d M B Y) : ∃ w A T t D V G,
      Check_d M b ω w ∧ Coll_names_d I B R B w X Y A T t ∧
      Row_stage_d M β D V b ∧ Row_next_d M α B R b A T t D V ∧ Reg_embed_d M B R B D V D G ∧
      (∀ p q, Entry_d M p q G ↔ M.mem p B ∧ q = p) ∧ Row_link_d I α B R D V ∧ Closed_d I D V D ω ∧
      ∀ k, (∀ p, M.mem p B → Row_supp_d I k ω p) → ∀ q, M.mem q D → Row_supp_d I k ω q := by
  obtain ⟨w, hw, hwN, _⟩ := zf_check_l M hZF h.base ω
  obtain ⟨A, T, t, hn⟩ := collapse_names_l h.order hZFC hwN hX hY
  have hb : b ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ h.base)
  obtain ⟨hP, ht, hClosed⟩ := collapse_names_closed_l h.order hZFC hω h.base hw (below_refl_l h.order h.base hb) hn
  obtain ⟨D, V, G, hStage, hNext, hG, hId, hLink, hSupp⟩ := row_successor_l hZF h hβ hn.1.1 hn.1.2.1 hn.1.2.2 hP ht
  exact ⟨w, A, T, t, D, V, G, hw, hn, hStage, hNext, hG, hId, hLink,
    row_next_closed_l hZFC h hNext hn.1.2.1 hP hω hw hc hClosed, fun k => hSupp I k ω hω⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 参数化塌缩的确定后继规则

固定旧 ω、源集和目标集参数；每阶段重新取其规范名称，再使用已证明唯一的
塌缩名称三元组和 Row_next 构造。规则输入保留完整历史，输出为真实坐标偏序。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_coll_d (I : kpair_convention_l.Interpretation M) (ω X Y α B R b D V : M.Domain) : Prop :=
  ∃ w x y A T t, Check_d M b ω w ∧ Check_d M b X x ∧ Check_d M b Y y ∧
    Coll_names_d I B R B w x y A T t ∧ Row_next_d M α B R b A T t D V

def row_coll_m {n} (ω X Y α B R b D V : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (check_m b.weaken.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5))
      (.conj (check_m b.weaken.weaken.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4))
        (.conj (check_m b.weaken.weaken.weaken.weaken.weaken.weaken Y.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3))
          (.conj (coll_names_m B.weaken.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken.weaken
            B.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
            (row_next_m α.weaken.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken.weaken
              R.weaken.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken.weaken
              (.bound 2) (.bound 1) .newest D.weaken.weaken.weaken.weaken.weaken.weaken V.weaken.weaken.weaken.weaken.weaken.weaken))))))))))
derive_free_closed row_coll_m

theorem row_coll_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (ω X Y α B R b D V : Term n) : Formula.satisfies ρ (row_coll_m ω X Y α B R b D V) ↔
      Row_coll_d I (ω.eval ρ) (X.eval ρ) (Y.eval ρ) (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [row_coll_m, Row_coll_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    check_sat_l M hE, coll_names_sat_l I hE, row_next_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

def Coll_rule_d (I : kpair_convention_l.Interpretation M) (ω X Y δ F G b D V : M.Domain) : Prop :=
  ∃ α B R, M.SuccessorOf δ α ∧ Entry_d M α B F ∧ Entry_d M α R G ∧ Row_coll_d I ω X Y α B R b D V

def coll_rule_m {n} (ω X Y δ F G b D V : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.conj (Formula.isSuccessor δ.weaken.weaken.weaken (.bound 2))
    (.conj (entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken)
      (.conj (entry_m (.bound 2) .newest G.weaken.weaken.weaken)
        (row_coll_m ω.weaken.weaken.weaken X.weaken.weaken.weaken Y.weaken.weaken.weaken
          (.bound 2) (.bound 1) .newest b.weaken.weaken.weaken D.weaken.weaken.weaken V.weaken.weaken.weaken))))))
derive_free_closed coll_rule_m

theorem coll_rule_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (ω X Y δ F G b D V : Term n) : Formula.satisfies ρ (coll_rule_m ω X Y δ F G b D V) ↔
      Coll_rule_d I (ω.eval ρ) (X.eval ρ) (Y.eval ρ) (δ.eval ρ) (F.eval ρ) (G.eval ρ) (b.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [coll_rule_m, Coll_rule_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, entry_sat_l M hE, row_coll_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

def coll_rule_s : BinarySchema 7 := {
  body := coll_rule_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }

theorem coll_rule_denote_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (ρ : Env M 3) (δ F G b D V) : coll_rule_s.denote (row_rule_env_l ρ δ F G b) D V ↔
      Coll_rule_d I (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) δ F G b D V :=
  coll_rule_sat_l I hE (((row_rule_env_l ρ δ F G b).push D).push V) _ _ _ _ _ _ _ _ _

end YesMetaZFC.Model.Forcing.Internal

/-! ## 参数化塌缩规则的存在、唯一性与闭性实例

三个旧参数的规范名称、后继名称三元组和坐标偏序都实际构造。
名称的字面唯一性使该原公式成为确定超限递归的真实规则。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem collapse_rule_l (ρ : Env M 3) (hω : M.IsOmega (ρ.bound 2)) (k : Bool) :
    Row_rule_d I k (ρ.bound 2) coll_rule_s ρ := by
  intro δ F G b h hSupp hSucc
  obtain ⟨α, hδ⟩ := hSucc
  obtain ⟨B, hB⟩ := (h.conditions.2.2 α).mp hδ.predecessor_mem
  obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp hδ.predecessor_mem
  have hs := h.stages α B R hB hR
  obtain ⟨w, hw, hwN, huw⟩ := zf_check_l M hZF hs.base (ρ.bound 2)
  obtain ⟨x, hx, hxN, hux⟩ := zf_check_l M hZF hs.base (ρ.bound 1)
  obtain ⟨y, hy, hyN, huy⟩ := zf_check_l M hZF hs.base (ρ.bound 0)
  obtain ⟨A, T, t, hn⟩ := collapse_names_l hs.order hZFC hwN hxN hyN
  have hb : b ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hs.base)
  obtain ⟨hP, ht, _⟩ := collapse_names_closed_l hs.order hZFC hω hs.base hw (below_refl_l hs.order hs.base hb) hn
  obtain ⟨μ, D, V, _, F', G', _, hNext, hd, _, _, hF, hG, hS⟩ :=
    row_system_successor_l hZF h hδ hB hR hn.1.1 hn.1.2.1 hn.1.2.2 hP ht
  have hDD := (hF δ D).mpr (Or.inr ⟨rfl, rfl⟩)
  have hVV := (hG δ V).mpr (Or.inr ⟨rfl, rfl⟩)
  refine ⟨D, V, (coll_rule_denote_l I hZFC.1 ρ δ F G b D V).mpr
    ⟨α, B, R, hδ, hB, hR, w, x, y, A, T, t, hw, hx, hy, hn, hd⟩,
    ⟨hNext.stages δ D V hDD hVV, ?_, (hS I k (ρ.bound 2) hω hSupp) δ D hDD⟩, ?_⟩
  · intro ξ C S hC hT
    exact hNext.links ξ δ C S D V ((hF ξ C).mpr (Or.inl hC)) ((hG ξ S).mpr (Or.inl hT)) hDD hVV
      (h.conditions.1.transitive.memberSubset ((h.conditions.2.2 ξ).mpr ⟨C, hC⟩))
  · intro D' V' h'
    obtain ⟨α', B', R', hδ', hB', hR', w', x', y', A', T', t', hw', hx', hy', hn', hd'⟩ :=
      (coll_rule_denote_l I hZFC.1 ρ δ F G b D' V').mp h'
    have he := Structure.SuccessorOf.predecessor_eq hZFC.1 (h.conditions.1.mem hδ.predecessor_mem) hδ hδ'
    subst α'
    have heB := h.conditions.2.1.2 α B B' hB hB'
    have heR := h.relations.2.1.2 α R R' hR hR'
    have hew := huw w' hw'
    have hex := hux x' hx'
    have hey := huy y' hy'
    subst B' R' w' x' y'
    obtain ⟨heA, heT, het⟩ := collapse_names_unique_l hs.order hZF hwN hxN hyN hn' hn
    subst A' T' t'
    exact row_next_unique_l M hZFC.1 hd' hd

/-- 同一实际塌缩规则提供闭迭代所需的完整名称证书。 -/
theorem collapse_rule_closed_l (ρ : Env M 3) (hω : M.IsOmega (ρ.bound 2)) :
    Row_cl_rule_d I (ρ.bound 2) coll_rule_s ρ := by
  intro δ F G b D V h _ hd
  obtain ⟨α, B, R, hδ, hB, hR, w, x, y, A, T, t, hw, _, _, hn, hNext⟩ :=
    (coll_rule_denote_l I hZFC.1 ρ δ F G b D V).mp hd
  have hs := h.stages α B R hB hR
  have hb : b ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hs.base)
  have hc := (collapse_names_closed_l hs.order hZFC hω hs.base hw (below_refl_l hs.order hs.base hb) hn).2.2
  exact ⟨α, B, R, hδ, hB, hR, A, T, t, w, hNext, hn.1.2.1, hw, hc⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 参数化塌缩的实际 proper 后继规则

同一原公式后继已经带有预序、内部 ω 和可数闭性名称；直接把这些真实证书
转为 properness。它可以与一般 proper 规则共用全部后继及完整区间设施。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem collapse_rule_pr_l (ρ : Env M 3) (hω : M.IsOmega (ρ.bound 2)) : Row_pr_rule_d I coll_rule_s ρ := by
  intro δ F G b D V h _ hd
  obtain ⟨α, B, R, hδ, hB, hR, w, x, y, A, T, t, hw, _, _, hn, hNext⟩ :=
    (coll_rule_denote_l I hZFC.1 ρ δ F G b D V).mp hd
  have hs := h.stages α B R hB hR
  have hb : b ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hs.base)
  have hp := below_refl_l hs.order hs.base hb
  obtain ⟨hP, _, hc⟩ := collapse_names_closed_l hs.order hZFC hω hs.base hw hp hn
  exact ⟨α, B, R, hδ, hB, hR, A, T, t, hn.1.2.1,
    closed_name_proper_l hs.order hZFC hω hs.base hw hp hn.1.1 hn.1.2.1 hP hc, hNext⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 任意内部长度的参数化可数闭塌缩迭代

两个集合参数与内部序数长度直接决定完整可数支撑迭代；全阶段闭性、全部前缀
区间以及各泛型扩张的 ZFC、序列与可数子集反射都由已实现规则自动取得。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem collapse_iteration_closed_l (X Y : M.Domain) {δ} (hδ : M.IsOrdinal δ) :
    ∃ ω b F G, M.IsOmega ω ∧
      Row_iteration_d I true ω b coll_rule_s (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y) δ F G ∧
      (∀ β, Row_cl_stage_d I ω F G β) ∧ ∀ β D V, Entry_d M β D F → Entry_d M β V G → Closed_d I D V D ω := by
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y
  obtain ⟨b, F, G, h, hi, hc⟩ := row_iteration_closed_exists_l hZFC hω hδ
    (collapse_rule_l hZFC ρ hω true) (collapse_rule_closed_l hZFC ρ hω)
  exact ⟨ω, b, F, G, hω, h, hi, hc⟩

/-- 一次构造全部闭阶段，并返回各泛型扩张中实数、旧目标序列及可数子集的实际旧原像。 -/
theorem collapse_iteration_preserves_l (X Y : M.Domain) {δ} (hδ : M.IsOrdinal δ) :
    ∃ ω b F G, M.IsOmega ω ∧
      ∃ h : Row_iteration_d I true ω b coll_rule_s (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y) δ F G,
        (∀ β, Row_cl_stage_d I ω F G β) ∧
        (∀ β D V, Entry_d M β D F → Entry_d M β V G → Closed_d I D V D ω) ∧
        ∀ β D V (hD : Entry_d M β D F) (hV : Entry_d M β V G) U (hU : Generic_d M D V D U),
          let O := (h.1.stages β D V hD hV).order
          let E := extension_l M hZF D V D U
          let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
          E.Models ZFC ∧ ∃ e : M.Domain → E.Domain,
            (∀ a s, Check_d M b a s → Qval_d M D V D U s (e a)) ∧
            (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧ Function.Injective e ∧ E.IsOmega (e ω) ∧
            (∀ x, E.MemberSubset x (e ω) → ∃ a, M.MemberSubset a ω ∧ e a = x) ∧
            (∀ A f, E.IsSetFunctionFromTo J f (e ω) (e A) →
              ∃ g, M.IsSetFunctionFromTo I g ω A ∧ e g = f) ∧
            (∀ A Y, E.MemberSubset Y (e A) → E.CardinalLessOrEqual J Y (e ω) →
              ∃ C, M.MemberSubset C A ∧ M.CardinalLessOrEqual I C ω ∧ e C = Y) ∧
            (∀ A, E.CardinalLessOrEqual J (e A) (e ω) ↔ M.CardinalLessOrEqual I A ω) ∧
            (∀ κ, M.IsHartogsNumber I κ ω → E.IsHartogsNumber J (e κ) (e ω)) ∧
            (∀ α, E.IsCofinality J (e ω) (e α) ↔ M.IsCofinality I ω α) ∧
            ∀ α cf, M.IsCofinality I cf α → M.mem ω cf → ∀ Y, E.MemberSubset Y (e α) →
              E.CardinalLessOrEqual J Y (e ω) → ∃ β, M.mem β α ∧ E.MemberSubset Y (e β) := by
  obtain ⟨ω, b, F, G, hω, h, hi, hc⟩ := collapse_iteration_closed_l hZFC X Y hδ
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y
  exact ⟨ω, b, F, G, hω, h, hi, hc, row_iteration_closed_preserves_l hZFC hω
    (collapse_rule_l hZFC ρ hω true) (collapse_rule_closed_l hZFC ρ hω) h⟩

/-- 同一参数化塌缩迭代同时返回全部闭区间、proper 阶段及任意种子的共同 N 区间引理。 -/
theorem collapse_iteration_pil_l (X Y : M.Domain) {δ} (hδ : M.IsOrdinal δ) :
    ∃ ω b F G, M.IsOmega ω ∧
      Row_iteration_d I true ω b coll_rule_s (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y) δ F G ∧
      (∀ β, Row_cl_stage_d I ω F G β) ∧
      (∀ β D V, Entry_d M β D F → Entry_d M β V G → Closed_d I D V D ω ∧ Proper_d I ω D V D) ∧
      ∀ A, M.CardinalLessOrEqual I A ω → ∃ χ H N,
        Hsub_d I ω χ H N ∧ M.MemberSubset A N ∧ M.mem δ N ∧
          ∀ β, M.mem β N → Row_pil_stage_d I F G b N β := by
  obtain ⟨ω, b, F, G, hω, h, hi, hc⟩ := collapse_iteration_closed_l hZFC X Y hδ
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y
  refine ⟨ω, b, F, G, hω, h, hi, (fun β D V hD hV => ?_),
    fun A ha => row_iteration_pr_l hZFC hω (collapse_rule_l hZFC ρ hω true) (collapse_rule_pr_l hZFC ρ hω) h ha⟩
  have hs := h.1.stages β D V hD hV
  exact ⟨hc β D V hD hV, closed_proper_l ⟨hs.order.refl, hs.order.trans⟩ hZFC hω (hc β D V hD hV)⟩

end YesMetaZFC.Model.Forcing.Internal
