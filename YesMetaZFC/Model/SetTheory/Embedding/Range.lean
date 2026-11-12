import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 实际内部初等映射的复合

复合图由替代构造，中间赋值由图复合构造；两次读取同一个内部公式码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem smap_comp_l (hZF : M.Models ZF) {ω c d e X Y Z j k : M.Domain}
    (h : Smap_d I ω c d X Y j) (g : Smap_d I ω d e Y Z k) : ∃ l, Smap_d I ω c e X Z l ∧
      ∀ x z, M.PairMember I x z l ↔ M.mem x X ∧ ∃ y, M.PairMember I x y j ∧ M.PairMember I y z k := by
  obtain ⟨l, hl, spec⟩ := ZF.exists_compositionFunction hZF I h.1.1 g.1.1
  have inj x y z (hx : M.PairMember I x z l) (hy : M.PairMember I y z l) : x = y := by
    obtain ⟨_, a, hxa, haz⟩ := (spec x z).mp hx
    obtain ⟨_, b, hyb, hbz⟩ := (spec y z).mp hy
    have eq := g.1.2 a b z haz hbz
    exact h.1.2 x y b (eq ▸ hxa) hyb
  obtain ⟨C, hC, read⟩ := h.2
  obtain ⟨D, hD, next⟩ := g.2
  refine ⟨l, ⟨⟨hl, inj⟩, C, hC, fun a f u ha hf hu hfu => ?_⟩, spec⟩
  obtain ⟨v, hv, assign⟩ := smap_assign_exists_l I hZF h.1.1 hf
  have compose : Smap_assign_d I ω k v u := by
    intro i hi y z hiy hyz
    obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
    obtain ⟨y', _, hxy⟩ := h.1.1.2.2 x hx
    have eq := hv.1.2 i y' y (assign i hi x y' hix hxy) hiy
    exact hfu i hi x z hix ((spec x z).mpr ⟨hx, y, eq ▸ hxy, hyz⟩)
  exact (read a f v ha hf hv assign).trans (next a v u ((hD a).mpr ((hC a).mp ha)) hv hu compose)

/-- 交换三角形中，两个到共同目标的初等图决定中间函数的完整初等性。 -/
theorem smap_factor_l (hZF : M.Models ZF) {ω c d e X Y Z f g j : M.Domain}
    (hg : Smap_d I ω c e X Z g) (hj : Smap_d I ω d e Y Z j) (hf : M.IsSetFunctionFromTo I f X Y)
    (comm : ∀ x y z, M.PairMember I x y f → M.PairMember I y z j → M.PairMember I x z g) :
    Smap_d I ω c d X Y f := by
  have inj a b y (ha : M.PairMember I a y f) (hb : M.PairMember I b y f) : a = b := by
    obtain ⟨z, _, hyz⟩ := hj.1.1.2.2 y (hf.output_mem_of_pairMember ha)
    exact hg.1.2 a b z (comm a y z ha hyz) (comm b y z hb hyz)
  obtain ⟨C, hC, read⟩ := hg.2
  obtain ⟨D, hD, next⟩ := hj.2
  refine ⟨⟨hf, inj⟩, C, hC, fun a t s ha ht hs assign => ?_⟩
  obtain ⟨u, hu, su⟩ := smap_assign_exists_l I hZF hj.1.1 hs
  have tu : Smap_assign_d I ω g t u := by
    intro i hi x z hix hxz
    obtain ⟨y, hy, hxy⟩ := hf.2.2 x (ht.output_mem_of_pairMember hix)
    obtain ⟨w, _, hyw⟩ := hj.1.1.2.2 y hy
    exact hg.1.1.1.2 x w z (comm x y w hxy hyw) hxz ▸ su i hi y w (assign i hi x y hix hxy) hyw
  exact (read a t u ha ht hu tu).trans (next a s u ((hD a).mpr ((hC a).mp ha)) hs hu su).symm

end YesMetaZFC.SetTheory.Internal

/-! ## 同一实际像的两个表示之间传递初等性

两张单射有同一像时，唯一值替代构造其比较双射；交换图保证复合后
恰好得到指定的嵌入，而不重新选择一个可能不同的目标或嵌入。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smap_same_range_l {ω X C N Y b c d R S f i g k : M.Domain}
    (hω : M.IsOmega ω) (hf : Smap_d I ω b c X C f) (hi : M.IsSetFunctionFromTo I i X N)
    (hg : M.IsSetInjectionFromTo I g C Y) (hk : M.IsSetInjectionFromTo I k N Y)
    (hc : Smdl_d I c C R) (hd : Smdl_d I d N S)
    (range : ∀ y, (∃ E, Rd_entry_d E y g) ↔ ∃ z, Rd_entry_d z y k)
    (rel : ∀ E H z w y y', Rd_entry_d E y g → Rd_entry_d H y' g → Rd_entry_d z y k → Rd_entry_d w y' k →
      (Rd_entry_d E H R ↔ Rd_entry_d z w S))
    (comm : ∀ x E z y, Rd_entry_d x E f → Rd_entry_d x z i → Rd_entry_d E y g → Rd_entry_d z y k) :
    Smap_d I ω b d X N i := by
  let ρ := (⟨fun _ => g, fun _ => g⟩ : Env M 1).push k
  let φ : BinarySchema 2 := {
    body := .existsE (.conj (rd_entry_m (.bound 2) .newest (.bound 4)) (rd_entry_m (.bound 1) .newest (.bound 3))) }
  have sat E z : φ.denote ρ E z ↔ ∃ y, Rd_entry_d E y g ∧ Rd_entry_d z y k := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := N)
    (fun E hE => by
      obtain ⟨y, _, hEy⟩ := hg.1.2.2 E hE
      obtain ⟨z, hzy⟩ := (range y).mp ⟨E, hEy⟩
      exact ⟨z, (sat E z).mpr ⟨y, hEy, hzy⟩⟩)
    (fun E _ z w hz hw => by
      obtain ⟨y, hEy, hzy⟩ := (sat E z).mp hz
      obtain ⟨y', hEy', hwy⟩ := (sat E w).mp hw
      exact hk.2 z w y hzy (hg.1.1.2 E y' y hEy' hEy ▸ hwy))
    (fun E z _ hz => ((sat E z).mp hz).elim fun _ hy => hk.1.input_mem_of_pairMember hy.2)
  have spec E z := (es E z).trans (and_congr_right fun _ => sat E z)
  have bij : M.IsSetBijectionFromTo I e C N := by
    refine ⟨⟨he, fun E H z hE hH => ?_⟩, fun z hz => ?_⟩
    · obtain ⟨_, y, hEy, hzy⟩ := (spec E z).mp hE
      obtain ⟨_, y', hHy, hzy'⟩ := (spec H z).mp hH
      exact hg.2 E H y hEy (hk.1.1.2 z y' y hzy' hzy ▸ hHy)
    · obtain ⟨y, _, hzy⟩ := hk.1.2.2 z hz
      obtain ⟨E, hEy⟩ := (range y).mpr ⟨z, hzy⟩
      exact ⟨E, hg.1.input_mem_of_pairMember hEy,
        (spec E z).mpr ⟨hg.1.input_mem_of_pairMember hEy, y, hEy, hzy⟩⟩
  have elem := smap_of_iso_l I hZF hω hc hd bij (fun E H z w hEz hHw => by
    obtain ⟨_, y, hEy, hzy⟩ := (spec E z).mp hEz
    obtain ⟨_, y', hHy, hwy⟩ := (spec H w).mp hHw
    exact rel E H z w y y' hEy hHy hzy hwy)
  obtain ⟨i', hi', cs⟩ := smap_comp_l I hZF hf elem
  have eq : i' = i := by
    apply (fn0_of_function_l (ZF.modelsKP hZF) hi'.1.1).ext_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hi)
    intro x hx
    obtain ⟨E, hE, hxE⟩ := hf.1.1.2.2 x hx
    obtain ⟨z, _, hxz⟩ := hi.2.2 x hx
    obtain ⟨y, _, hEy⟩ := hg.1.2.2 E hE
    exact ⟨z, (cs x z).mpr ⟨hx, E, hxE, (spec E z).mpr ⟨hE, y, hEy, comm x E z y hxE hxz hEy⟩⟩, hxz⟩
  exact eq ▸ hi'

end YesMetaZFC.SetTheory.Internal
