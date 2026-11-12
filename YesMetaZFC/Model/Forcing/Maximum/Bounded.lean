import YesMetaZFC.Model.Forcing.Names.PairConstruction
import YesMetaZFC.SetTheory.Choice
import YesMetaZFC.Model.Forcing.Maximum.UniqueRules
import YesMetaZFC.Model.Forcing.Maximum.WitnessPool
import YesMetaZFC.Model.Forcing.Maximum.Normal

/-! # 按内部序数枚举选择名称

在每个条件以下，取仍可能属于目标集合的最小枚举指标，再加强条件实现该隶属。
较早指标已不可能出现，因此泛型滤子得到的选择与目标名称的不同呈现无关。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Poss_mem_d (B R z F p i t : M.Domain) : Prop :=
  ∃ s, Entry_d M i s F ∧ ∃ q, Below_d M B R z q p ∧ Mem_force_d M B R z q s t

def Min_mem_d (B R z F κ p s t : M.Domain) : Prop :=
  ∃ i, M.mem i κ ∧ Entry_d M i s F ∧ Mem_force_d M B R z p s t ∧
    ∀ j, M.mem j i → ¬ Poss_mem_d M B R z F p j t

def poss_mem_m {n} (B R z F p i t : Term n) : Formula 1 n :=
  .existsE (.conj (entry_m i.weaken .newest F.weaken)
    (.existsE (.conj (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest p.weaken.weaken)
      (mem_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest (.bound 1) t.weaken.weaken))))
derive_free_closed poss_mem_m

def min_mem_m {n} (B R z F κ p s t : Term n) : Formula 1 n :=
  .existsE (.conj (.mem .newest κ.weaken) (.conj (entry_m .newest s.weaken F.weaken)
    (.conj (mem_force_m B.weaken R.weaken z.weaken p.weaken s.weaken t.weaken)
      (.forallE (.imp (.mem .newest (.bound 1)) (.neg
        (poss_mem_m B.weaken.weaken R.weaken.weaken z.weaken.weaken F.weaken.weaken
          p.weaken.weaken .newest t.weaken.weaken)))))))
derive_free_closed min_mem_m

theorem poss_mem_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z F p i t : Term n) :
    Formula.satisfies ρ (poss_mem_m B R z F p i t) ↔
      Poss_mem_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) (p.eval ρ) (i.eval ρ) (t.eval ρ) := by
  simp only [poss_mem_m, Poss_mem_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, below_sat_l M hE, mem_force_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push,
    Term.eval_bound_zero_push]

theorem min_mem_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z F κ p s t : Term n) :
    Formula.satisfies ρ (min_mem_m B R z F κ p s t) ↔
      Min_mem_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) (κ.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [min_mem_m, Min_mem_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_mem_iff, entry_sat_l M hE, mem_force_sat_l M hE, poss_mem_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push,
    Term.eval_bound_zero_push]

theorem min_mem_defined_l (hE : Extensional M) (B R z F κ t : M.Domain) :
    Defined_d M (fun p => ∃ s, Min_mem_d M B R z F κ p s t) := by
  let ρ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F).push κ).push t
  let φ : UnarySchema 6 := {
    body := .existsE (min_mem_m (.bound 7) (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 1) .newest (.bound 2)) }
  refine ⟨6, φ, ρ, fun p => ?_⟩
  simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, min_mem_sat_l M hE]
  rfl

variable {M} {B R z : M.Domain} (O : Cond_order_d M B R z)
include O

theorem poss_mem_extend_l {F p q i t} (hp : M.mem p B) (hq : Below_d M B R z q p)
    (h : Poss_mem_d M B R z F q i t) : Poss_mem_d M B R z F p i t := by
  obtain ⟨s, hs, r, hr, hm⟩ := h
  exact ⟨s, hs, r, below_trans_l O hp hr hq, hm⟩

theorem min_mem_lower_l (F κ s t : M.Domain) : Lower_d M B R z (fun p => Min_mem_d M B R z F κ p s t) := by
  rintro p q hp hq ⟨i, hi, hs, hm, hn⟩
  exact ⟨i, hi, hs, (regular_mem_l O s t).1 p q hp hq hm,
    fun j hj h => hn j hj (poss_mem_extend_l O hp hq h)⟩

/-- 候选指标组成模型内集合，其内部最小元给出稠密的最早隶属条件。 -/
theorem min_mem_dense_l (hZF : M.Models ZF) {F κ p i s t}
    (hκ : M.IsOrdinal κ) (hi : M.mem i κ) (his : Entry_d M i s F)
    (hm : Mem_force_d M B R z p s t) :
    Dense_d M B R z (fun q => ∃ a, Min_mem_d M B R z F κ q a t) p := by
  intro q hq
  let ρ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F).push q).push t
  let φ : UnarySchema 6 := {
    body := poss_mem_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest (.bound 1) }
  obtain ⟨J, hJ⟩ := ZF.separation_exists_d hZF φ ρ κ
  have hj j : M.mem j J ↔ M.mem j κ ∧ Poss_mem_d M B R z F q j t := by
    rw [hJ j]
    simp only [φ, poss_mem_sat_l M hZF.1]
    rfl
  have hiJ := (hj i).mpr ⟨hi, s, his, q, below_refl_l O hq.1 hq.2.1,
    (regular_mem_l O s t).1 p q hm.1 hq hm⟩
  obtain ⟨k, hkJ, hk⟩ := hκ.wellOrder.least J (fun j hjJ => ((hj j).mp hjJ).1) ⟨i, hiJ⟩
  obtain ⟨hkκ, a, hka, r, hr, ham⟩ := (hj k).mp hkJ
  refine ⟨r, hr, a, k, hkκ, hka, ham, fun j hjk hposs => ?_⟩
  have hjκ := hκ.transitive k hkκ j hjk
  have hjJ := (hj j).mpr ⟨hjκ, poss_mem_extend_l O hq.1 hr hposs⟩
  rcases hk j hjJ with he | hkj
  · have he := hZF.1.eq_of_same_members k j he
    exact hκ.wellOrder.linear.irrefl j hjκ (he ▸ hjk)
  · exact hκ.wellOrder.linear.irrefl j hjκ
      (hκ.wellOrder.linear.trans j hjκ k hkκ j hjκ hjk hkj)

/-- 对同一目标，共同加强上的最小候选严格相同；仅消费枚举图的单值性。 -/
theorem min_mem_compat_l (hE : Extensional M) {F κ p q r s t A}
    (hκ : M.IsOrdinal κ) (hf : ∀ i s t, Entry_d M i s F → Entry_d M i t F → s = t)
    (hrp : Below_d M B R z r p) (hrq : Below_d M B R z r q)
    (hs : Min_mem_d M B R z F κ p s A) (ht : Min_mem_d M B R z F κ q t A) : s = t := by
  obtain ⟨i, hi, his, hsm, hsi⟩ := hs
  obtain ⟨j, hj, hjt, htm, htj⟩ := ht
  rcases hκ.wellOrder.linear.compare i hi j hj with he | hij | hji
  · have he := hE.eq_of_same_members i j he
    subst j
    exact hf i s t his hjt
  · exact False.elim (htj i hij ⟨s, his, r, hrq, (regular_mem_l O s A).1 p r hsm.1 hrp hsm⟩)
  · exact False.elim (hsi j hji ⟨t, hjt, r, hrp, (regular_mem_l O t A).1 q r htm.1 hrq htm⟩)

/-- 相同解释的两个目标名称给出同一个被选元素，即使枚举或名称有重复呈现。 -/
theorem min_mem_unique_l (hZF : M.Models ZF) {U : M.Domain → Prop}
    (hU : Generic_d M B R z U) {F κ S p q s t a b} {x y w : Name_quot_l M B R z U}
    (hκ : M.IsOrdinal κ)
    (hf : M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F κ S)
    (hp : U p) (hq : U q) (hs : Qval_d M B R z U s x) (ha : Qval_d M B R z U a y)
    (ht : Qval_d M B R z U t w) (hb : Qval_d M B R z U b w)
    (hm : Min_mem_d M B R z F κ p s t) (hn : Min_mem_d M B R z F κ q a b) : x = y := by
  obtain ⟨i, hi, his, hmt, hmi⟩ := hm
  obtain ⟨j, hj, hja, hnb, hnj⟩ := hn
  have hm := (qval_mem_forcing_l O hZF hU hs ht).mp ⟨p, hp, hmt⟩
  have hn := (qval_mem_forcing_l O hZF hU ha hb).mp ⟨q, hq, hnb⟩
  have impossible {i j s t p} {x : Name_quot_l M B R z U}
      (hi : Entry_d M i s F) (hij : M.mem i j) (hp : U p)
      (hs : Qval_d M B R z U s x) (ht : Qval_d M B R z U t w) (hx : x ∈ w)
      (hn : ∀ k, M.mem k j → ¬ Poss_mem_d M B R z F p k t) : False := by
    obtain ⟨q, hq, hm⟩ := (qval_mem_forcing_l O hZF hU hs ht).mpr hx
    obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
    have hr' := hU.proper r hr
    exact hn i hij ⟨s, hi, r, ⟨hr'.1, hr'.2, hrp⟩,
      (regular_mem_l O s t).1 q r hm.1 ⟨hr'.1, hr'.2, hrq⟩ hm⟩
  rcases hκ.wellOrder.linear.compare i hi j hj with he | hij | hji
  · have he := hZF.1.eq_of_same_members i j he
    subst j
    have he := hf.1.2 i s a his hja
    subst a
    exact qval_unique_l hs ha
  · exact False.elim (impossible his hij hq hs hb hm hnj)
  · exact False.elim (impossible hja hji hp ha ht hn hmi)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部名称的统一成员见证

在目标名称的内部支撑上作序数枚举，以最小可能指标选择成员，再混合这些选择。
得到的一个名称同时服务于所有条件，不将 Prop 存在性导出为不可计算选择实例。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
include O hZFC

/-- 每个内部名称都有统一成员名称：任何条件能迫使它有成员时，该名称即为成员。 -/
theorem member_maximum_l {A} (hA : Name_d M B A) : ∃ t, Name_d M B t ∧
    ∀ p s, Mem_force_d M B R z p s A → Mem_force_d M B R z p t A := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨W, hAW, hW⟩ := hA
  obtain ⟨κ, F, hκ, hf, hsur⟩ := ZFC.ordinal_enum_l hZFC I W
  let ρ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F).push κ).push A
  let φ : BinarySchema 6 := {
    body := min_mem_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) .newest (.bound 1) (.bound 2) }
  have hφ s p : φ.denote ρ s p ↔ Min_mem_d M B R z F κ p s A :=
    min_mem_sat_l M hZF.1 ((ρ.push s).push p) _ _ _ _ _ _ _ _
  obtain ⟨t, ht, _, hm⟩ := mixing_l O hZF φ ρ hW (by
    intro p q s t r _ _ hs _ hp hq hrp hrq
    have he := min_mem_compat_l O hZF.1 hκ hf.1.2 hrp hrq ((hφ s p).mp hp) ((hφ t q).mp hq)
    exact he ▸ eq_force_refl_l O hZF hrp.1 ⟨W, hs, hW⟩)
  refine ⟨t, ht, fun p s hp => mem_force_dense_l O hp.1 ?_⟩
  intro q hq
  obtain ⟨r, a, c, hr, hac, hrc, _⟩ := hp.2 q hq
  have haW := (supp_entry_l M hW hAW hac).1
  have ha : Name_d M B a := ⟨W, haW, hW⟩
  obtain ⟨i, hi, hia⟩ := hsur a haW
  have har := mem_force_entry_l O hZF hr.1 ha (supp_entry_l M hW hAW hac).2 hac hrc
  obtain ⟨v, hv, a, hmin⟩ := min_mem_dense_l O hZF hκ hi hia har r (below_refl_l O hr.1 hr.2.1)
  have haW : M.mem a W := hf.output_mem_of_pairMember hmin.choose_spec.2.1
  have ha : Name_d M B a := ⟨W, haW, hW⟩
  have he := hm v a hv.1 haW ((hφ a v).mpr hmin)
  exact ⟨v, below_trans_l O hq.1 hv hr, mem_force_left_l O hZF ha ht ⟨W, hAW, hW⟩
    (eq_force_symm_l hZF ht ha he) hmin.choose_spec.2.2.1⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原公式的内部最大值原理

先由原收集模式把可能见证收紧到一个内部集合，再构造见证名称集并选择其统一
成员名称。一个名称同时实现全部正条件上的存在力迫，不假设外部泛型或良基性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 加权名称的每个条目满足正文时，被迫属于它的名称也满足正文。 -/
private theorem predicate_name_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {n}
    (φ : Formula 1 (n+1)) (ρ : Env M n) (hρ : ∀ v : Term n, Name_d M B (v.eval ρ)) {A}
    (hA : ∀ s b, Entry_d M s b A → Name_d M B s ∧ M.mem b B ∧ Forces_d M B R z φ (ρ.push s) b)
    {p t} (hp : M.mem p B) (hz : p ≠ z) (ht : Name_d M B t) (hm : Mem_force_d M B R z p t A) :
    Forces_d M B R z φ (ρ.push t) p := by
  have push {s} (hs : Name_d M B s) : ∀ v : Term (n+1), Name_d M B (v.eval (ρ.push s)) := by
    intro v
    cases v with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i
  apply (forces_regular_l O hZF φ _ (push ht)).2 p hp hz
  intro q hq
  obtain ⟨r, s, b, hr, hsb, hrb, he⟩ := hm.2 q hq
  obtain ⟨hs, hb, hφ⟩ := hA s b hsb
  have hφr := (forces_regular_l O hZF φ _ (push hs)).1 b r hb ⟨hr.1, hr.2.1, hrb⟩ hφ
  have hc := forces_congr_below_l O hZF φ (ρ.push t) (ρ.push s) (push ht) (push hs) hr.1 (fun v => by
    cases v with
    | free i => exact eq_force_refl_l O hZF hr.1 (hρ (.free i))
    | bound i => exact Fin.cases he (fun i => eq_force_refl_l O hZF hr.1 (hρ (.bound i))) i)
  exact ⟨r, hr, (hc r (below_refl_l O hr.1 hr.2.1)).mpr hφr⟩

/-- 一次生成原公式的最大值见证名称；仅要求实际有限参数均为名称。 -/
private theorem maximum_raw_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {n}
    (φ : UnarySchema n) (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) :
    ∃ t, Name_d M B t ∧ ∀ p, M.mem p B → p ≠ z →
      (Forces_d M B R z (.existsE φ.body) ρ p ↔ Forces_d M B R z φ.body (ρ.push t) p) := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hen := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he
  let η : Env M n := ⟨ρ.bound, fun _ => e⟩
  have hη : ∀ t : Term n, Name_d M B (t.eval η) := by
    intro t
    cases t with
    | free _ => exact hen
    | bound i => exact hρ i
  obtain ⟨A, hA, hSound, hPool⟩ := witness_pool_l hZF φ η
  obtain ⟨t, ht, hmax⟩ := member_maximum_l O hZFC hA
  have hηt : ∀ v : Term (n+1), Name_d M B (v.eval (η.push t)) := by
    intro v
    cases v with
    | free i => exact hη (.free i)
    | bound i => exact Fin.cases ht (fun i => hη (.bound i)) i
  have hr := forces_regular_l O hZF φ.body (η.push t) hηt
  refine ⟨t, ht, fun p hp hz => ?_⟩
  have hm : Forces_d M B R z (.existsE φ.body) η p ↔ Forces_d M B R z φ.body (η.push t) p := by
    constructor
    · intro hex
      apply hr.2 p hp hz
      intro q hq
      obtain ⟨r, hqr, v, hv, hφ⟩ := forces_exists_dense_l hZF.1 hex q hq
      obtain ⟨s, hsa⟩ := hPool r hqr.1 v hv hφ
      have hsN := (name_entry_l M hA hsa).1
      have hmem := hmax r s (mem_force_entry_l O hZF hqr.1 hsN hqr.1 hsa (O.refl r hqr.1))
      refine ⟨r, hqr, predicate_name_l O hZF φ.body η hη ?_ hqr.1 hqr.2.1 ht hmem⟩
      intro a b hab
      exact ⟨(name_entry_l M hA hab).1, (name_entry_l M hA hab).2, hSound a b hab⟩
    · exact forces_exists_intro_l O hZF.1 ht hr.1 hp
  exact (forces_env_l hZF.1 (.existsE φ.body)
    (by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed) ρ η (fun _ => rfl) p).trans
    (hm.trans (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push t) (η.push t) (fun _ => rfl) p).symm)

/-- 最大值名称直接返回规范固定点，供后继名称与递归装配统一使用。 -/
theorem maximum_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {n}
    (φ : UnarySchema n) (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) :
    ∃ t, Name_d M B t ∧
      Norm_name_d M (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B R z t t ∧
      ∀ p, M.mem p B → p ≠ z →
        (Forces_d M B R z (.existsE φ.body) ρ p ↔ Forces_d M B R z φ.body (ρ.push t) p) := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨t, ht, hMax⟩ := maximum_raw_l O hZFC φ ρ hρ
  obtain ⟨q, _, hNorm, hq, he⟩ := norm_name_exists_l O hZF ht
  exact ⟨q, hq, hNorm, fun p hp hz => (hMax p hp hz).trans
    (forces_name_congr_l O hZF φ ρ hρ ht hq hp hz (eq_force_symm_l hZF hq ht (he p hp hz)))⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 固定条件上的库内见证选择

一般最大值原理先给出见证，再用 ZF 的同条件等值代表将它送回确定名称库。
一个名称同时实现所有正条件上的有界存在式；首阶段条件不需加强。
选择公理仅用于统一成员选择，名称库的构造和混合闭合仍只需 ZF。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 任意原公式的有界存在式，在原条件上由同一库内名称实现。 -/
theorem name_pool_maximum_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {n}
    (φ : UnarySchema n) (ρ : Env M n) (i : Fin n) (hρ : ∀ j, Name_d M B (ρ.bound j))
    {t W} (hW : Name_pool_d M B (ρ.bound i) t W) :
    ∃ s, M.mem s W ∧ ∀ p, M.mem p B → p ≠ z →
      (Forces_d M B R z (.existsE (.conj (.mem .newest (Term.bound i).weaken) φ.body)) ρ p ↔
        Mem_force_d M B R z p s (ρ.bound i) ∧ Forces_d M B R z φ.body (ρ.push s) p) := by
  let hZF := ZFC.models_zf_l hZFC
  let η : Env M n := ⟨ρ.bound, fun _ => ρ.bound i⟩
  have hη : ∀ a : Term n, Name_d M B (a.eval η) := by
    intro a
    cases a with
    | free _ => exact hρ i
    | bound j => exact hρ j
  let χ : UnarySchema n := {
    body := .conj (.mem .newest (Term.bound i).weaken) φ.body
    freeClosed := by
      simp only [Definitional.Formula.FreeClosed]
      exact ⟨⟨rfl, rfl⟩, φ.freeClosed⟩ }
  obtain ⟨v, hv, _, hMax⟩ := maximum_l O hZFC χ η hρ
  obtain ⟨s, hsW, hRep⟩ := name_pool_represent_l O hZF hW hv
  have hs : Name_d M B s := ⟨W, hsW, hW.closed⟩
  have hηs : ∀ a : Term (n+1), Name_d M B (a.eval (η.push s)) := by
    intro a
    cases a with
    | free j => exact hη (.free j)
    | bound j => exact Fin.cases hs (fun j => hη (.bound j)) j
  refine ⟨s, hsW, fun p hp hz => ?_⟩
  have hm : Forces_d M B R z (.existsE χ.body) η p ↔ Forces_d M B R z χ.body (η.push s) p := by
    constructor
    · intro hex
      have hvχ := (hMax p hp hz).mp hex
      have hvA := (forces_mem_l hZF.1 _ _ _ p).mp ((forces_conj_l _ _ _ p).mp hvχ).1
      exact (forces_name_congr_l O hZF χ η hρ hv hs hp hz
        (eq_force_symm_l hZF hs hv (hRep p hvA))).mp hvχ
    · exact forces_exists_intro_l O hZF.1 hs (forces_regular_l O hZF χ.body _ hηs).1 hp
  have hc := (forces_env_l hZF.1 (.existsE χ.body)
    (by simpa only [Definitional.Formula.FreeClosed] using χ.freeClosed) ρ η (fun _ => rfl) p).trans
    (hm.trans (forces_env_l hZF.1 χ.body χ.freeClosed (ρ.push s) (η.push s) (fun _ => rfl) p).symm)
  exact hc.trans ((forces_conj_l _ _ _ p).trans
    (and_congr (forces_mem_l hZF.1 _ _ _ p) Iff.rfl))

end YesMetaZFC.Model.Forcing.Internal
