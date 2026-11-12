import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion
import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.SetTheory.Descriptive.Coding.Prefix
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift
import YesMetaZFC.SetTheory.Descriptive.Tree.HistoryTree
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeWellFounded
import YesMetaZFC.SetTheory.Descriptive.Tree.RetractionFixed
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeShift

/-! # 成员满嵌入保持全部内部有限列

对目标模型内部 ω 上的实际公式归纳：零列来自地模型，后继列由地前缀及地末项
追加得到。因此即使内部长度外部非标准，扩张也不新增取值于地集合的有限列。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

/-- 地有限列空间的规范像就是目标的全部有限列空间；不假设内部自然数标准。 -/
theorem image_fseq_l {ω X S} (hω : M.IsOmega ω) (hw : N.IsOmega (e ω))
    (hS : Fseq_space_d I ω X S) : Fseq_space_d J (e ω) (e X) (e S) := by
  let ρ : Env N 2 := (⟨fun _ => e S, fun _ => e S⟩ : Env N 1).push (e X)
  let φ : UnarySchema 2 := { body := .forallE (.imp
    (Formula.isFunctionFromTo kpair_convention_l .newest (.bound 1) (.bound 2))
    (.mem .newest (.bound 3))) }
  have hφ n : φ.denote ρ n ↔ ∀ f, N.IsSetFunctionFromTo J f n (e X) → N.mem f (e S) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isFunctionFromTo_iff J hN.1, Formula.satisfies_mem_iff]
    rfl
  have lift : ∀ n, N.mem n (e ω) → ∀ f, N.IsSetFunctionFromTo J f n (e X) → N.mem f (e S) := by
    apply hw.induction (fun n => ∀ f, N.IsSetFunctionFromTo J f n (e X) → N.mem f (e S))
    · obtain ⟨D, hD⟩ := ZF.separation_exists_d hN φ ρ (e ω)
      exact ⟨D, fun n => (hD n).trans (and_congr_right fun _ => hφ n)⟩
    · intro n hn f hf
      obtain ⟨a, ha, haω⟩ := hω.1.1
      have hfa : M.IsSetFunctionFromTo I a a X :=
        ⟨(Structure.IsSequenceOfLength.empty I ha).2.1,
          (Structure.IsSequenceOfLength.empty I ha).2.2, fun i hi => (ha i hi).elim⟩
      have haS := (hS a).mpr ⟨a, haω, hfa⟩
      have hEmpty : ∀ y, ¬ N.mem y f := by
        intro y hy
        obtain ⟨i, x, hp⟩ := hf.1.1 y hy
        exact hn i (hf.input_mem_of_pairMember ⟨y, hp, hy⟩)
      have hEq : e a = f := hN.1.eq_of_same_members _ _ (fun y => iff_of_false
        (fun hy => (he a y).mp hy |>.elim fun c hc => ha c hc.1) (hEmpty y))
      exact (he S f).mpr ⟨a, haS, hEq⟩
    · intro m hm ih n hn f hf
      obtain ⟨a, haω, rfl⟩ := (he ω m).mp hm
      obtain ⟨g, hg⟩ := ZF.exists_restriction hN J f (e a)
      have hgf := hg.isSetFunctionFromTo hf (fun i hi => (hn i).mpr (Or.inl hi))
      obtain ⟨s, hsS, hsg⟩ := (he S g).mp (ih g hgf)
      obtain ⟨k, hkω, hsk⟩ := (hS s).mp hsS
      have hsk' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he hsk
      have hka : k = a := hi (hsk'.2.1.eq hN.1 (hsg.symm ▸ hgf.2.1))
      subst k
      obtain ⟨y, hy, hfy⟩ := hf.2.2 (e a) hn.predecessor_mem
      obtain ⟨x, hx, rfl⟩ := (he X y).mp hy
      obtain ⟨b, hb, hbω⟩ := hω.1.2 a haω
      obtain ⟨t, ht, hts⟩ := Structure.IsSequenceOfLength.exists_append (value := x)
        (ZF.modelsKP hM) I ⟨(hω.isOrdinal (ZF.modelsKP hM)).mem haω, hsk.1, hsk.2.1⟩
        ((hω.isOrdinal (ZF.modelsKP hM)).mem hbω) hb
      have htX : M.IsSetFunctionFromTo I t b X := by
        refine ⟨ht.2.1, ht.2.2, fun i hi => ?_⟩
        obtain ⟨v, hv⟩ := (ht.2.2 i).mp hi
        refine ⟨v, ?_, hv⟩
        rcases (hts i v).mp hv with hv | ⟨_, rfl⟩
        · exact hsk.output_mem_of_pairMember hv
        · exact hx
      have ht' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he htX
      have hEq : e t = f := by
        apply ht'.1.1.eq_of_pairMember_iff hN.1 hf.1.1
        intro i v
        change Entry_d N i v (e t) ↔ Entry_d N i v f
        rw [image_entries_l e he ht.2.1.1 i v]
        constructor
        · rintro ⟨j, w, hjw, rfl, rfl⟩
          rcases (hts j w).mp hjw with hjw | ⟨rfl, rfl⟩
          · have hv := (image_entries_l e he hsk.1.1 (e j) (e w)).mpr ⟨j, w, hjw, rfl, rfl⟩
            exact ((hg.2 (e j) (e w)).mp (hsg ▸ hv)).2
          · exact hfy
        · intro hv
          rcases (hn i).mp (hf.input_mem_of_pairMember hv) with him | him
          · have hv := hsg.symm ▸ (hg.2 i v).mpr ⟨him, hv⟩
            obtain ⟨j, w, hjw, hj, hw⟩ := (image_entries_l e he hsk.1.1 i v).mp hv
            exact ⟨j, w, (hts j w).mpr (Or.inl hjw), hj, hw⟩
          · have hei := hN.1.eq_of_same_members i (e a) him
            subst i
            exact ⟨a, x, (hts a x).mpr (Or.inr ⟨rfl, rfl⟩), rfl, hf.1.2 (e a) (e x) v hfy hv⟩
      exact (he S f).mpr ⟨t, (hS t).mpr ⟨b, hbω, htX⟩, hEq⟩
  intro f
  constructor
  · intro hf
    obtain ⟨s, hs, rfl⟩ := (he S f).mp hf
    obtain ⟨n, hn, hs⟩ := (hS s).mp hs
    exact ⟨e n, (image_member_l e hi he).mpr hn, image_function_l e hi he hs⟩
  · rintro ⟨n, hn, hf⟩
    exact lift n hn f hf

/-- 任意内部有限地字母列连同精确长度一并拉回。 -/
theorem image_finite_function_pull_l {ω A : M.Domain} {n f : N.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) (hn : N.mem n (e ω))
    (ff : N.IsSetFunctionFromTo J f n (e A)) :
    ∃ k s, M.mem k ω ∧ M.IsSetFunctionFromTo I s k A ∧ e k = n ∧ e s = f := by
  obtain ⟨F,space⟩ := ZF.fseq_space_exists_l I hM hw A
  obtain ⟨s,hs,eq⟩ := (he F f).mp ((image_fseq_l hM hN e hi he hw hw' space f).mpr ⟨n,hn,ff⟩)
  obtain ⟨k,hk,fs⟩ := (space s).mp hs
  have moved := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fs
  exact ⟨k,s,hk,fs,moved.2.1.eq hN.1 (eq.symm ▸ ff.2.1),eq⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范嵌入下内部语法码的绝对性

成员满嵌入保持指令字母表；全部内部有限列的保持随后排除新的有限程序。
因此公式码全集也精确保持，无需假定模型的 ω 外部标准。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
section Codes
variable (hM : M.Models KP) (hN : N.Models KP) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair hM)
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair hN)
include hM hN hi he

omit hM hN in
theorem image_num_l (hEM : Extensional M) (hEN : Extensional N)
    {k x} (hx : @Num_d M k x) : @Num_d N k (e x) := by
  induction k generalizing x with
  | zero => exact fun y hy => (he x y).mp hy |>.elim fun a ha => hx a ha.1
  | succ k ih =>
    obtain ⟨a, ha, hx⟩ := hx
    exact ⟨e a, ih ha, image_successor_l (hEN := hEN) e hi he hEM hx⟩

theorem image_sop_l {k c i j} : Sop_d J k (e c) (e i) (e j) ↔ Sop_d I k c i j := by
  have forward {c} (h : Sop_d I k c i j) : Sop_d J k (e c) (e i) (e j) := by
    obtain ⟨a, o, ho, ha, hc⟩ := h
    exact ⟨e a, e o, image_num_l e hi he hM.1 hN.1 ho, image_kpair_l e he ha, image_kpair_l e he hc⟩
  refine ⟨fun h => ?_, forward⟩
  obtain ⟨d, hd⟩ := sop_exists_l I hM k i j
  obtain ⟨a, o, ho, ha, hc⟩ := h
  obtain ⟨b, p, hp, hb, hd'⟩ := forward hd
  have hop := num_unique_l hN.1 ho hp
  have hab := kpair_unique_l N hN.1 ha hb
  subst p b
  exact hi (kpair_unique_l N hN.1 hc hd') ▸ hd

theorem image_sfm_node_l {ω r c} : Sfm_node_d J (e ω) (e r) (e c) ↔ Sfm_node_d I ω r c := by
  have cases (k : Nat) (A B : M.Domain) :
      (∃ i j, Sop_d J k (e c) i j ∧ N.mem i (e A) ∧ N.mem j (e B)) ↔
      ∃ i j, Sop_d I k c i j ∧ M.mem i A ∧ M.mem j B := by
    constructor
    · rintro ⟨i, j, hc, hiA, hjB⟩
      obtain ⟨a, ha, rfl⟩ := (he A i).mp hiA
      obtain ⟨b, hb, rfl⟩ := (he B j).mp hjB
      exact ⟨a, b, (image_sop_l hM hN e hi he).mp hc, ha, hb⟩
    · rintro ⟨i, j, hc, hiA, hjB⟩
      exact ⟨e i, e j, (image_sop_l hM hN e hi he).mpr hc,
        (image_member_l e hi he).mpr hiA, (image_member_l e hi he).mpr hjB⟩
  exact or_congr (cases 0 ω ω) (or_congr (cases 1 ω ω) (or_congr (cases 2 r r) (cases 3 ω r)))

end Codes

variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

theorem image_sfm_l {ω n F X} (hω : M.IsOmega ω) (hw : N.IsOmega (e ω))
    (hn : M.mem n ω) (hF : M.IsSetFunctionFromTo I F n X) :
    Sfm_d J (e ω) (e n) (e F) ↔ Sfm_d I ω n F := by
  have hFn := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he hF
  have hn' := (image_member_l e hi he).mpr hn
  constructor
  · intro h
    refine ⟨hn, ⟨(hω.isOrdinal (ZF.modelsKP hM)).mem hn, hF.1, hF.2.1⟩, fun r c hc => ?_⟩
    exact (image_sfm_node_l (ZF.modelsKP hM) (ZF.modelsKP hN) e hi he).mp
      (h.2.2 (e r) (e c) ((image_entries_l e he hF.1.1 (e r) (e c)).mpr ⟨r, c, hc, rfl, rfl⟩))
  · intro h
    refine ⟨hn', ⟨(hw.isOrdinal (ZF.modelsKP hN)).mem hn', hFn.1, hFn.2.1⟩, fun r c hc => ?_⟩
    obtain ⟨i, a, hia, rfl, rfl⟩ := (image_entries_l e he hF.1.1 r c).mp hc
    exact (image_sfm_node_l (ZF.modelsKP hM) (ZF.modelsKP hN) e hi he).mpr (h.2.2 i a hia)

/-- 包含非标准程序的内部公式码全集在成员满嵌入下精确保持。 -/
theorem image_scode_l {ω C} (hω : M.IsOmega ω) (hw : N.IsOmega (e ω))
    (hC : Scode_d I ω C) : Scode_d J (e ω) (e C) := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hM I ω ω
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hM I ω P
  have hP' := image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he hP
  have hQ' := image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he hQ
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hM hω Q
  have hS' := image_fseq_l hM hN e hi he hω hw hS
  have graph {n F} (hF : Sfm_d I ω n F) : M.IsSetFunctionFromTo I F n Q := by
    refine ⟨hF.2.1.2.1, hF.2.1.2.2, fun i hi => ?_⟩
    obtain ⟨c, hic⟩ := (hF.2.1.2.2 i).mp hi
    exact ⟨c, sfm_node_mem_l I hM hω hP hQ (hω.transitive (ZF.modelsKP hM) n hF.1 i hi) (hF.2.2 i c hic), hic⟩
  intro a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := (he C a).mp ha
    obtain ⟨n, F, k, ha, hF, hk⟩ := (hC b).mp hb
    exact ⟨e n, e F, e k, image_kpair_l e he ha,
      (image_sfm_l hM hN e hi he hω hw hF.1 (graph hF)).mpr hF, (image_member_l e hi he).mpr hk⟩
  · rintro ⟨n, F, k, ha, hF, hk⟩
    have hFn : N.IsSetFunctionFromTo J F n (e Q) := by
      refine ⟨hF.2.1.2.1, hF.2.1.2.2, fun i hi => ?_⟩
      obtain ⟨c, hic⟩ := (hF.2.1.2.2 i).mp hi
      exact ⟨c, sfm_node_mem_l J hN hw hP' hQ' (hw.transitive (ZF.modelsKP hN) n hF.1 i hi) (hF.2.2 i c hic), hic⟩
    obtain ⟨G, hGS, rfl⟩ := (he S F).mp ((hS' F).mpr ⟨n, hF.1, hFn⟩)
    obtain ⟨m, hm, hG⟩ := (hS G).mp hGS
    have hG' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he hG
    have hmn := hG'.2.1.eq hN.1 hFn.2.1
    subst n
    obtain ⟨j, hj, rfl⟩ := (he m k).mp hk
    obtain ⟨b, hb⟩ := (I).total G j
    have hba := kpair_unique_l N hN.1 (image_kpair_l e he hb) ha
    exact (he C a).mpr ⟨b, (hC b).mpr ⟨m, G, j, hb,
      (image_sfm_l hM hN e hi he hω hw hm hG).mp hF, hj⟩, hba⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 新无限列的每个内部有限前缀都有真实地原像 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

theorem ground_prefix_l {ω A k : M.Domain} {f : N.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (ff : N.IsSetFunctionFromTo J f (e ω) (e A)) (hk : M.mem k ω) :
    ∃ s, M.IsSetFunctionFromTo I s k A ∧ N.IsRestrictionOf J (e s) f (e k) := by
  obtain ⟨F, space⟩ := ZF.fseq_space_exists_l I hM hw A
  obtain ⟨s, fs, cut, _⟩ := ds_prefix_l J hN hw' ff ((image_member_l e hi he).mpr hk)
  have hs := (image_fseq_l hM hN e hi he hw hw' space s).mpr ⟨e k, (image_member_l e hi he).mpr hk, fs⟩
  obtain ⟨s₀, hs₀, eq⟩ := (he F s).mp hs; subst s
  obtain ⟨n, _, fn⟩ := (space s₀).mp hs₀
  have fn' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fn
  have eq := hi (fn'.2.1.eq hN.1 fs.2.1); subst n
  exact ⟨s₀, fn, cut⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 地模型有限合法走法的双向保持 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

theorem image_end_l {ω X F t h a : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (space : Fseq_space_d I ω X F) (ht : M.mem t F) (hh : M.mem h F) :
    Fseq_end_d I ω t h a ↔ Fseq_end_d J (e ω) (e t) (e h) (e a) := by
  let ρ : Env M 5 := ⟨fun i => [ω, X, t, h, a].get i, fun _ => ω⟩
  exact (ds_end_bound_sat_l hM ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) hw space ht hh).symm.trans
    ((delta0_image_l e hi he (ds_end_bound_delta_l (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) ρ).trans
      (ds_end_bound_sat_l hN (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
        hw' (image_fseq_l hM hN e hi he hw hw' space) ((image_member_l e hi he).mpr ht) ((image_member_l e hi he).mpr hh)))

theorem image_admit_l {ω X F L h a : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (space : Fseq_space_d I ω X F) (legal : M.MemberSubset L F) (hh : M.mem h F) :
    Cg_admit_d hM ω L h a ↔ Cg_admit_d hN (e ω) (e L) (e h) (e a) := by
  let ρ : Env M 5 := ⟨fun i => [ω, X, L, h, a].get i, fun _ => ω⟩
  have space' := image_fseq_l hM hN e hi he hw hw' space
  have legal' : N.MemberSubset (e L) (e F) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (he L y).mp hy
    exact (image_member_l e hi he).mpr (legal x hx)
  exact (cg_admit_bound_sat_l hM ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) hw space legal hh).symm.trans
    ((delta0_image_l e hi he (cg_admit_bound_delta_l (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) ρ).trans
      (cg_admit_bound_sat_l hN (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
        hw' space' legal' ((image_member_l e hi he).mpr hh)))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 地嵌入保持内部有限算术与奇偶

直接搬运原递归图及其限制；自然数长度排除极限分支。证明不在地模型中
对目标模型的外部谓词作归纳，也不要求内部自然数在外部标准。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Descriptive
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hM hN hi he

omit hM hN in
theorem image_subset_iff_l {a b : M.Domain} : N.MemberSubset (e a) (e b) ↔ M.MemberSubset a b :=
  ⟨fun h x hx => (image_member_l e hi he).mp (h (e x) ((image_member_l e hi he).mpr hx)),
    fun h y hy => (he a y).mp hy |>.elim fun x hx => hx.2 ▸ (image_member_l e hi he).mpr (h x hx.1)⟩

theorem image_ord_l {α : M.Domain} (hα : M.IsOrdinal α) : N.IsOrdinal (e α) := by
  let ρ : Env M 1 := ⟨fun _ => α, fun _ => α⟩
  exact (KP.ord0_sat_l (ZF.modelsKP hN) (image_env_l e ρ) .newest).mp
    ((delta0_image_l e hi he (KP.ord0_delta_l .newest) ρ).mp ((KP.ord0_sat_l (ZF.modelsKP hM) ρ .newest).mpr hα))

theorem image_sequence_l {f n : M.Domain} (seq : M.IsSequenceOfLength I f n) :
    N.IsSequenceOfLength J (e f) (e n) := by
  obtain ⟨R, range⟩ := ZF.exists_range_of_setFunction hM I seq.2.1 seq.2.2
  have fn : M.IsSetFunctionFromTo I f n R := ⟨seq.2.1, seq.2.2, fun i hi => by
    obtain ⟨x, ix⟩ := (seq.2.2 i).mp hi
    exact ⟨x, (range x).mpr ⟨i, ix⟩, ix⟩⟩
  have fn' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fn
  exact ⟨image_ord_l hM hN e hi he seq.1, fn'.1, fn'.2.1⟩

theorem image_restriction_l {g f n : M.Domain} (rel : M.IsSetRelation I f) (cut : M.IsRestrictionOf I g f n) :
    N.IsRestrictionOf J (e g) (e f) (e n) := by
  refine ⟨?_, fun x y => ?_⟩
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := (he g z).mp hz
    obtain ⟨a, b, code⟩ := cut.1 p hp
    exact ⟨e a, e b, image_kpair_l e he code⟩
  · constructor
    · intro ent
      obtain ⟨a, b, ab, rfl, rfl⟩ := (image_entries_l e he cut.1 x y).mp ent
      exact ⟨(image_member_l e hi he).mpr ((cut.2 a b).mp ab).1,
        (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 a b f).mp ((cut.2 a b).mp ab).2⟩
    · rintro ⟨xn, ent⟩
      obtain ⟨a, b, ab, rfl, rfl⟩ := (image_entries_l e he rel x y).mp ent
      exact (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 a b g).mp
        ((cut.2 a b).mpr ⟨(image_member_l e hi he).mp xn, ab⟩)

theorem image_last_sequence_l {f x : M.Domain} (last : M.IsSuccessorLengthSequenceWithLast I f x) :
    N.IsSuccessorLengthSequenceWithLast J (e f) (e x) := by
  obtain ⟨i, oi, n, succ, seq, ent⟩ := last
  exact ⟨e i, image_ord_l hM hN e hi he oi, e n, image_successor_l (hEN := hN.1) e hi he hM.1 succ,
    image_sequence_l hM hN e hi he seq, (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i x f).mp ent⟩

/-- 已实现的加法、乘法阶段共用同一次有限递归图搬运。 -/
theorem image_finite_recursion_l {ω n x : M.Domain} {P : M.Domain → M.Domain → Prop} {Q : N.Domain → N.Domain → Prop}
    (hw : M.IsOmega ω) (hn : M.mem n ω)
    (step : ∀ f x i, M.mem i ω → M.IsSequenceOfLength I f i → P f x → Q (e f) (e x))
    (val : M.IsRecursionValue I P n x) : N.IsRecursionValue J Q (e n) (e x) := by
  obtain ⟨f, run, last⟩ := val
  refine ⟨e f, ⟨image_sequence_l hM hN e hi he run.1, ?_⟩, step f x n hn run.1 last⟩
  intro i hin y iy
  obtain ⟨i₀, hi₀, rfl⟩ := (he n i).mp hin
  obtain ⟨j, y₀, jy, ej, ey⟩ := (image_entries_l e he run.1.2.1.1 (e i₀) y).mp iy
  have eq := hi ej; subst j y
  obtain ⟨g, cut, value⟩ := run.2 i₀ hi₀ y₀ jy
  have sub := run.1.1.transitive i₀ hi₀
  exact ⟨e g, image_restriction_l hM hN e hi he run.1.2.1.1 cut,
    step g y₀ i₀ (hw.transitive (ZF.modelsKP hM) n hn i₀ hi₀)
      ⟨run.1.1.mem hi₀, cut.isSetFunction run.1.2.1, cut.isDomainOf run.1.2.2 sub⟩ value⟩

theorem image_nat_add_l {ω a b x : M.Domain} (hw : M.IsOmega ω) (hb : M.mem b ω)
    (sum : M.IsOrdinalAddition I x a b) : N.IsOrdinalAddition J (e x) (e a) (e b) := by
  apply image_finite_recursion_l hM hN e hi he hw hb ?_ sum
  intro f x i hiω seq step
  rcases step with ⟨⟨z, fz, hz⟩, rfl⟩ | ⟨v, last, succ⟩ | ⟨k, limit, fk, _⟩
  · exact Or.inl ⟨⟨e z, image_sequence_l hM hN e hi he fz,
      fun y hy => (he z y).mp hy |>.elim fun v hv => hz v hv.1⟩, rfl⟩
  · exact Or.inr (Or.inl ⟨e v, image_last_sequence_l hM hN e hi he last,
      image_successor_l (hEN := hN.1) e hi he hM.1 succ⟩)
  · have eq := fk.2.2.eq hM.1 seq.2.2
    exact (KP.mem_irrefl_d (ZF.modelsKP hM) i (hw.subset_limitOrdinal (ZF.modelsKP hM) (eq ▸ limit) i hiω)).elim

theorem image_even_l {ω n : M.Domain} (hw : M.IsOmega ω) :
    Gm_even_d I ω n ↔ Gm_even_d J (e ω) (e n) := by
  constructor
  · rintro ⟨k, hk, sum⟩
    exact ⟨e k, (image_member_l e hi he).mpr hk, image_nat_add_l hM hN e hi he hw hk sum⟩
  · rintro ⟨k, hk, sum⟩
    obtain ⟨k₀, hk₀, rfl⟩ := (he ω k).mp hk
    obtain ⟨s, hs, _⟩ := ZF.ordinalAddition_existsUnique hM I k₀ (hw.members_areOrdinals (ZF.modelsKP hM) k₀ hk₀)
    obtain ⟨t, _, unique⟩ := ZF.ordinalAddition_existsUnique hN J (e k₀)
      (image_ord_l hM hN e hi he (hw.members_areOrdinals (ZF.modelsKP hM) k₀ hk₀))
    have eq := hi ((unique (e s) (image_nat_add_l hM hN e hi he hw hk₀ hs)).trans (unique (e n) sum).symm)
    exact ⟨k₀, hk₀, eq ▸ hs⟩

theorem image_nat_mul_l {ω a b x : M.Domain} (hw : M.IsOmega ω) (ha : M.mem a ω) (hb : M.mem b ω)
    (mul : M.IsOrdinalMultiplication I x a b) : N.IsOrdinalMultiplication J (e x) (e a) (e b) := by
  apply image_finite_recursion_l hM hN e hi he hw hb ?_ mul
  intro f x i hiω seq step
  have oa := hw.members_areOrdinals (ZF.modelsKP hM) a ha
  rcases step with ⟨no, _⟩ | ⟨_, step⟩
  · exact (no oa).elim
  apply Or.inr ∘ And.intro (image_ord_l hM hN e hi he oa)
  rcases step with ⟨⟨z, fz, hz⟩, hx⟩ | ⟨v, last, sum⟩ | ⟨k, limit, fk, _⟩
  · exact Or.inl ⟨⟨e z, image_sequence_l hM hN e hi he fz,
      fun y hy => (he z y).mp hy |>.elim fun v hv => hz v hv.1⟩,
      fun y hy => (he x y).mp hy |>.elim fun v hv => hx v hv.1⟩
  · exact Or.inr (Or.inl ⟨e v, image_last_sequence_l hM hN e hi he last, image_nat_add_l hM hN e hi he hw ha sum⟩)
  · have eq := fk.2.2.eq hM.1 seq.2.2
    exact (KP.mem_irrefl_d (ZF.modelsKP hM) i (hw.subset_limitOrdinal (ZF.modelsKP hM) (eq ▸ limit) i hiω)).elim

theorem image_nat_div_l {ω i c n r : M.Domain} (hw : M.IsOmega ω) (hc : M.mem c ω) (hn : M.mem n ω)
    (div : M.IsOrdinalDivision I i c n r) : N.IsOrdinalDivision J (e i) (e c) (e n) (e r) := by
  obtain ⟨on, rc, p, mul, sum⟩ := div
  exact ⟨image_ord_l hM hN e hi he on, (image_member_l e hi he).mpr rc, e p,
    image_nat_mul_l hM hN e hi he hw hc hn mul, image_nat_add_l hM hN e hi he hw (hw.transitive (ZF.modelsKP hM) c hc r rc) sum⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 树的字母逆像与规范地模型嵌入交换

有限节点和字母映射的图边均有地来源；复合图的唯一性排除新增逆像节点。
无限分支仍在目标模型中重新量化，不假定两模型具有相同分支。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

theorem image_fseq_recode_l {f X Y n p q : M.Domain} (ff : M.IsSetFunctionFromTo I f X Y)
    (fp : M.IsSetFunctionFromTo I p n X) (h : Fseq_recode_d I f p q) : Fseq_recode_d J (e f) (e p) (e q) := by
  have fq := h.function_l I hM ff fp
  have fq' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fq
  refine ⟨fq'.1.1, fun i y => ?_⟩
  constructor
  · intro iy
    obtain ⟨j, z, jz, rfl, rfl⟩ := (image_entries_l e he fq.1.1 i y).mp iy
    obtain ⟨x, jx, xz⟩ := (h.2 j z).mp jz
    exact ⟨e x, (image_entries_l e he fp.1.1 (e j) (e x)).mpr ⟨j, x, jx, rfl, rfl⟩,
      (image_entries_l e he ff.1.1 (e x) (e z)).mpr ⟨x, z, xz, rfl, rfl⟩⟩
  · rintro ⟨x, ix, xy⟩
    obtain ⟨j, a, ja, rfl, rfl⟩ := (image_entries_l e he fp.1.1 i x).mp ix
    obtain ⟨b, z, bz, eq, rfl⟩ := (image_entries_l e he ff.1.1 (e a) y).mp xy
    have eq := hi eq; subst b
    exact (image_entries_l e he fq.1.1 (e j) (e z)).mpr ⟨j, z, (h.2 j z).mpr ⟨a, ja, bz⟩, rfl, rfl⟩

theorem image_tree_pullback_l {ω X Y f F T S : M.Domain} (ff : M.IsSetFunctionFromTo I f X Y)
    (space : Fseq_space_d I ω X F) (pull : Tr_pull_d I f F T S) : Tr_pull_d J (e f) (e F) (e T) (e S) := by
  intro p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := (he S p).mp hp
    obtain ⟨hqF, r, hr, qr⟩ := (pull q).mp hq
    obtain ⟨n, _, fq⟩ := (space q).mp hqF
    exact ⟨(image_member_l e hi he).mpr hqF, e r, (image_member_l e hi he).mpr hr,
      image_fseq_recode_l hM hN e hi he ff fq qr⟩
  · rintro ⟨hp, r, hr, pr⟩
    obtain ⟨q, hq, rfl⟩ := (he F p).mp hp
    obtain ⟨s, hs, rfl⟩ := (he T r).mp hr
    obtain ⟨n, _, fq⟩ := (space q).mp hq
    obtain ⟨t, _, qt⟩ := ZF.fseq_compose_l I hM ff fq
    have eq := hi ((image_fseq_recode_l hM hN e hi he ff fq qt).unique_l J hN.1 pr)
    subst t
    exact (image_member_l e hi he).mpr ((pull q).mpr ⟨hq, s, hs, qt⟩)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 旧历史的策略服从性与截面条件保持

目标中的限制图由源中的实际限制图唯一确定。因此有限历史的策略控制条件
逐项绝对，证明不假定策略在目标中仍获胜。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem image_follows_l {b : Bool} {ω K σ f : M.Domain} (rel : M.IsSetRelation I f) :
    Cg_follows_d J b (e ω) (e K) (e σ) (e f) ↔ Cg_follows_d I b ω K σ f := by
  have turn i : (if b then N.mem (e i) (e K) else ¬ N.mem (e i) (e K)) ↔
      (if b then M.mem i K else ¬ M.mem i K) := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, image_member_l e hi he]
  constructor
  · intro follows i hin own h cut a value
    exact (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 h a σ).mpr
      (follows (e i) ((image_member_l e hi he).mpr hin) ((turn i).mpr own) (e h)
        (image_restriction_l hM hN e hi he rel cut) (e a)
        ((image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i a f).mp value))
  · intro follows i hin own h cut a value
    obtain ⟨k, hk, rfl⟩ := (he ω i).mp hin
    obtain ⟨g, cut'⟩ := ZF.exists_restriction hM I f k
    have eq := cut.eq hN.1 (image_restriction_l hM hN e hi he rel cut')
    subst h
    obtain ⟨l, z, lz, eq, rfl⟩ := (image_entries_l e he rel (e k) a).mp value
    have eq := hi eq; subst l
    exact (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 g z σ).mp
      (follows k hk ((turn k).mp own) g cut' z lz)

theorem image_hg_strategy_l {b : Bool} {ω X F K σ S : M.Domain}
    (space : Fseq_space_d I ω X F)
    (read : ∀ s, M.mem s S ↔ M.mem s F ∧ Cg_follows_d I b ω K σ s) :
    ∀ s, N.mem s (e S) ↔ N.mem s (e F) ∧ Cg_follows_d J b (e ω) (e K) (e σ) s := by
  intro s
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := (he S s).mp hs
    obtain ⟨hf, follows⟩ := (read t).mp ht
    obtain ⟨_, _, ft⟩ := (space t).mp hf
    exact ⟨(image_member_l e hi he).mpr hf, (image_follows_l hM hN e hi he ft.1.1).mpr follows⟩
  · rintro ⟨hs, follows⟩
    obtain ⟨t, ht, rfl⟩ := (he F s).mp hs
    obtain ⟨_, _, ft⟩ := (space t).mp ht
    exact (image_member_l e hi he).mpr ((read t).mpr
      ⟨ht, (image_follows_l hM hN e hi he ft.1.1).mp follows⟩)

theorem image_hg_section_l {F x S : M.Domain}
    (read : ∀ s, M.mem s S ↔ M.mem s F ∧ M.MemberSubset s x) :
    ∀ s, N.mem s (e S) ↔ N.mem s (e F) ∧ N.MemberSubset s (e x) := by
  intro s
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := (he S s).mp hs
    exact ⟨(image_member_l e hi he).mpr ((read t).mp ht).1,
      (image_subset_iff_l e hi he).mpr ((read t).mp ht).2⟩
  · rintro ⟨hs, sub⟩
    obtain ⟨t, ht, rfl⟩ := (he F s).mp hs
    exact (image_member_l e hi he).mpr ((read t).mpr ⟨ht, (image_subset_iff_l e hi he).mp sub⟩)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 地面树秩在传递外模型中的保持

秩证书是有界公式；成员满覆盖的嵌入逐式保持证书。无限分支在目标模型
中重新量化，由实际秩排除，不要求两模型具有相同的实数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
include hi he

theorem image_tree_l {F T : M.Domain} (tree : Tree_d F T) : Tree_d (e F) (e T) := by
  refine ⟨(image_subset_iff_l e hi he).mpr tree.1, ?_⟩
  intro s hs t ht sub
  obtain ⟨a, ha, rfl⟩ := (he T s).mp hs
  obtain ⟨b, hb, rfl⟩ := (he F t).mp ht
  exact (image_member_l e hi he).mpr (tree.2 a ha b hb ((image_subset_iff_l e hi he).mp sub))

include hM hN in
theorem image_tree_rank_l {ω X T α H : M.Domain} (rank : Cg_rank_d ω X T α H) :
    Cg_rank_d (e ω) (e X) (e T) (e α) (e H) := by
  let ρ : Env M 5 := ⟨fun i => [H, α, T, X, ω].get i, fun _ => ω⟩
  exact (cg_rank0_sat_l (ZF.modelsKP hN) (image_env_l e ρ) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).mp
    ((delta0_image_l e hi he (cg_rank0_delta_l (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) ρ).mp
      ((cg_rank0_sat_l (ZF.modelsKP hM) ρ (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).mpr rank))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 历史收缩与首层补全在实际扩张中保持

有限图仍来自原模型。局部提升时，先在原模型追加同一字母，追加的唯一性
识别扩张中的给定后继；不假设扩张中的无限对局来自原模型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal SetTheory.Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem image_retract_l {ω A F R π : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) (space : Fseq_space_d I ω A F)
    (tree : Tree_d F R) (retract : Tr_retract_d I ω A F R π) :
    Tr_retract_d J (e ω) (e A) (e F) (e R) (e π) := by
  have ff := fn0_function_l (ZF.modelsKP hM) retract.function
  have fn := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he ff
  have finite := image_fseq_l hM hN e hi he hw hw' space
  have entries := image_entries_l e he ff.1.1
  have entry := image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have typed n s : Fn0_d n A s ↔ Fn0_d (e n) (e A) (e s) := by
    let ρ : Env M 3 := ⟨Fin.cases s (Fin.cases A (fun _ => n)),fun _ => A⟩
    have tr := delta0_image_l e hi he (fn0_delta_l (.bound 2) (.bound 1) (.bound 0)) ρ
    simpa only [fn0_sat_l hM.1,fn0_sat_l hN.1] using! tr
  refine ⟨fn0_of_function_l (ZF.modelsKP hN) fn,?_,?_,?_,?_⟩
  · intro n s t hn fs st
    obtain ⟨k,hk,rfl⟩ := (he ω n).mp hn
    obtain ⟨a,b,ab,rfl,rfl⟩ := (entries s t).mp st
    exact (typed k b).mp (retract.length k a b hk ((typed k a).mpr fs) ab)
  · intro s t u v su tv sub
    obtain ⟨a,b,ab,rfl,rfl⟩ := (entries s u).mp su
    obtain ⟨c,d,cd,rfl,rfl⟩ := (entries t v).mp tv
    exact (image_subset_iff_l e hi he).mpr
      (retract.monotone a c b d ab cd ((image_subset_iff_l e hi he).mp sub))
  · intro s hs
    obtain ⟨a,ha,rfl⟩ := (he R s).mp hs
    exact (entry a a π).mp (retract.fixed a ha)
  · intro s r t a u sr ht endt endu
    obtain ⟨s₀,r₀,sr₀,rfl,rfl⟩ := (entries s r).mp sr
    obtain ⟨t₀,ht₀,rfl⟩ := (he R t).mp ht
    have htF := tree.1 t₀ ht₀
    obtain ⟨_,_,ft⟩ := (finite (e t₀)).mp ((image_member_l e hi he).mpr htF)
    have ending := endt
    obtain ⟨_,_,ending⟩ := ending
    obtain ⟨a₀,ha₀,rfl⟩ := (he A a).mp (ft.output_mem_of_pairMember ending.last_value)
    have et := (image_end_l hM hN e hi he hw hw' space htF
      (tree.1 r₀ (retract.function.bound_l sr₀).2)).mpr endt
    obtain ⟨n,hn,fs⟩ := (space s₀).mp (retract.function.bound_l sr₀).1
    obtain ⟨m,u₀,hm,fu,eu⟩ := ZF.fseq_end_exists_l I hM hw hn fs ha₀
    have eu' := (image_end_l hM hN e hi he hw hw' space ((space u₀).mpr ⟨m,hm,fu⟩)
      (retract.function.bound_l sr₀).1).mp eu
    have eq := fseq_end_rebuild_l J hN.1 eu' endu
    exact eq ▸ (entry u₀ t₀ π).mp (retract.lift s₀ r₀ t₀ a₀ u₀ sr₀ ht₀ et eu)

theorem image_first_l {ω A F one T W : M.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) (space : Fseq_space_d I ω A F)
    (fill : Tr_first_d hM F one T W) : Tr_first_d hN (e F) (e one) (e T) (e W) := by
  let ρ : Env M 6 := ⟨fun i => [ω,A,F,one,T,W].get i,fun _ => ω⟩
  exact (tr_first_bound_sat_l hN (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)
    (image_fseq_l hM hN e hi he hw hw' space)).mp
    ((delta0_image_l e hi he (tr_first_bound_delta_l (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)) ρ).mp
      ((tr_first_bound_sat_l hM ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) space).mpr fill))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 首项拼接和移位树沿地嵌入保持

只传递地有限节点的图方程。扩张中的全部无限分支另由目标模型内部的移位定理处理。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

theorem image_cons_l {z a s t : M.Domain} (fs : M.IsSetRelation I s) (h : Cons_d I z a s t) :
    Cons_d J (e z) (e a) (e s) (e t) := by
  refine ⟨?_, fun j x => ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := (he t q).mp hq
    obtain ⟨i, v, c⟩ := h.1 p hp
    exact ⟨e i, e v, image_kpair_l e he c⟩
  · constructor
    · intro jx
      obtain ⟨i, y, iy, rfl, rfl⟩ := (image_entries_l e he h.1 j x).mp jx
      rcases (h.2 i y).mp iy with ⟨rfl, rfl⟩ | ⟨k, ky, sk⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨e k, (image_entries_l e he fs (e k) (e y)).mpr ⟨k, y, ky, rfl, rfl⟩,
          image_successor_l (hEN := hN.1) e hi he hM.1 sk⟩
    · rintro (⟨rfl, rfl⟩ | ⟨i, ix, sj⟩)
      · exact (image_entries_l e he h.1 (e z) (e a)).mpr ⟨z, a, (h.2 z a).mpr (Or.inl ⟨rfl, rfl⟩), rfl, rfl⟩
      · obtain ⟨k, y, ky, rfl, rfl⟩ := (image_entries_l e he fs i x).mp ix
        obtain ⟨l, sl⟩ := KP.exists_successor (ZF.modelsKP hM) k
        have eq := (image_successor_l (hEN := hN.1) e hi he hM.1 sl).eq hN.1 sj
        exact eq ▸ (image_entries_l e he h.1 (e l) (e y)).mpr ⟨l, y, (h.2 l y).mpr (Or.inr ⟨k, ky, sl⟩), rfl, rfl⟩

theorem image_tree_shift_l {ω X z F T S : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (hz : ∀ x, ¬ M.mem x z) (space : Fseq_space_d I ω X F) (subT : M.MemberSubset T F)
    (shift : Tr_shift_d I z F T S) : Tr_shift_d J (e z) (e F) (e T) (e S) := by
  have hz' y (hy : N.mem y (e z)) : False := (he z y).mp hy |>.elim fun x hx => hz x hx.1
  intro t
  constructor
  · intro ht
    obtain ⟨q, hq, rfl⟩ := (he S t).mp ht
    obtain ⟨hqF, tail⟩ := (shift q).mp hq
    refine ⟨(image_member_l e hi he).mpr hqF, ?_⟩
    rcases tail with rfl | ⟨a, s, hs, cs⟩
    · exact Or.inl rfl
    · obtain ⟨_, _, fs⟩ := (space s).mp (subT s hs)
      exact Or.inr ⟨e a, e s, (image_member_l e hi he).mpr hs, image_cons_l hM hN e hi he fs.1.1 cs⟩
  · rintro ⟨ht, tail⟩
    obtain ⟨q, hq, rfl⟩ := (he F t).mp ht
    apply (image_member_l e hi he).mpr
    refine (shift q).mpr ⟨hq, ?_⟩
    rcases cons_cases_l I hM hw space hz hq with eq | ⟨a, s, _, hs, cs⟩
    · exact Or.inl eq
    · rcases tail with eq | ⟨b, r, hr, cr⟩
      · exact (cons_ne_empty_l I hz cs (hi eq)).elim
      · obtain ⟨t, ht, rfl⟩ := (he T r).mp hr
        obtain ⟨n, hn, fs⟩ := (space s).mp hs
        obtain ⟨m, hm, ft⟩ := (space t).mp (subT t ht)
        have eq := (cons_injective_l J hN hw' hz' ((image_member_l e hi he).mpr hn) ((image_member_l e hi he).mpr hm)
          (image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fs)
          (image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he ft)
          (image_cons_l hM hN e hi he fs.1.1 cs) cr).2
        exact Or.inr ⟨a, s, (hi eq).symm ▸ ht, cs⟩

end YesMetaZFC.Model.Forcing.Internal
