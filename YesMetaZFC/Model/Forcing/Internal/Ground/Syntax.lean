import YesMetaZFC.Model.Forcing.Internal.Ground.FiniteSequence
import YesMetaZFC.Model.SetTheory.Internal.FormulaCode

/-! # 规范嵌入下内部语法码的绝对性

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
    refine ⟨hn, ⟨(hω.isOrdinal hM).mem hn, hF.1, hF.2.1⟩, fun r c hc => ?_⟩
    exact (image_sfm_node_l (ZF.modelsKP hM) (ZF.modelsKP hN) e hi he).mp
      (h.2.2 (e r) (e c) ((image_entries_l e he hF.1.1 (e r) (e c)).mpr ⟨r, c, hc, rfl, rfl⟩))
  · intro h
    refine ⟨hn', ⟨(hw.isOrdinal hN).mem hn', hFn.1, hFn.2.1⟩, fun r c hc => ?_⟩
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
    exact ⟨c, sfm_node_mem_l I hM hω hP hQ (hω.transitive hM n hF.1 i hi) (hF.2.2 i c hic), hic⟩
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
      exact ⟨c, sfm_node_mem_l J hN hw hP' hQ' (hw.transitive hN n hF.1 i hi) (hF.2.2 i c hic), hic⟩
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
