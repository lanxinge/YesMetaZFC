import YesMetaZFC.Model.SetTheory.Internal.RelationUniformCode

/-! # 全内部公式的统一函数图代码

把有序对成员条件与原公式合取，再要求所选图是 D 上、某个源内集合中的函数。
函数图坐标在原支撑之外，函数值和原公式的两个变量使用不同坐标。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Suniform_d (X R E F n r i j f D C B : M.Domain) : Prop := Fn0_d D C B ∧
  ∀ x y, Rd_entry_d x y B → Sbin_d I X R E F n r i j f x y

theorem sfm_uniform_l (hZF : M.Models ZF) {ω n F r i j s t u σ b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hσ : M.mem σ ω)
    (hi : M.mem i σ) (hj : M.mem j σ) (hs : M.mem s σ) (ht : M.mem t σ) (hu : M.mem u σ)
    (hij : i ≠ j) (hsi : s ≠ i) (hti : t ≠ i) (htj : t ≠ j) (hst : s ≠ t) (hus : u ≠ s) (hut : u ≠ t)
    (hb : Sbound_d I F b) (htb : ¬ M.mem t b) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D f →
      (Ssat_d I X R E G m k f ↔ ∃ B C, M.mem B X ∧ M.mem C X ∧ Suniform_d I X R E F n r i j f D C B) := by
  obtain ⟨m, G, k, build, read⟩ := sfm_uniform_raw_l I hZF hω hF hr hσ hi hj hs ht hu hij hsi hti htj hst hus hut hb htb
  refine ⟨m, G, k, build, fun X R E c f D hX hm hE hf hD => ?_⟩
  let N := smdl_structure_l I (R := R) hm.1.2.1
  let D₀ : N.Domain := ⟨D, ((hE f).mp hf).output_mem_of_pairMember hD⟩
  have ext := smem_ext_l I hm.1 hm.2 hX hZF.1
  have fn (B C : N.Domain) : Fn0_d D₀ C B ↔ Fn0_d D C.val B.val := by
    let ρ : Env N 3 := ⟨Fin.cases D₀ (Fin.cases C (fun _ => B)), fun _ => B⟩
    exact (fn0_sat_l ext ρ .newest (.bound 1) (.bound 2)).symm.trans
      ((smem_delta_image_l I hm hX (fn0_delta_l ..) ρ).trans (fn0_sat_l hZF.1 ..))
  have entry (x y B : N.Domain) : Rd_entry_d x y B ↔ Rd_entry_d x.val y.val B.val := by
    let ρ : Env N 3 := ⟨Fin.cases x (Fin.cases y (fun _ => B)), fun _ => B⟩
    exact (rd_entry0_sat_l ext ρ .newest (.bound 1) (.bound 2)).symm.trans
      ((smem_delta_image_l I hm hX (rd_entry0_delta_l ..) ρ).trans (rd_entry0_sat_l hZF.1 ..))
  rw [read X R E c f hm.1 D₀ ext hE hf hD]
  constructor
  · rintro ⟨B, C, hBC, truth⟩
    have ff := (fn B C).mp hBC
    refine ⟨B.val, C.val, B.property, C.property, ff, fun x y hxy => ?_⟩
    exact truth ⟨x, hX D D₀.property x (ff.bound_l hxy).1⟩ ⟨y, hX C.val C.property y (ff.bound_l hxy).2⟩
      ((entry _ _ B).mpr hxy)
  · rintro ⟨B, C, hB, hC, ff, truth⟩
    exact ⟨⟨B, hB⟩, ⟨C, hC⟩, (fn ⟨B, hB⟩ ⟨C, hC⟩).mpr ff,
      fun x y hxy => truth x.val y.val ((entry x y ⟨B, hB⟩).mp hxy)⟩

end YesMetaZFC.SetTheory.Internal
