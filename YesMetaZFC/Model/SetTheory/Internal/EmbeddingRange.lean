import YesMetaZFC.Model.SetTheory.Internal.EmbeddingComposition
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 同一实际像的两个表示之间传递初等性

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
