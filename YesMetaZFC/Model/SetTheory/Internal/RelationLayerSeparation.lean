import YesMetaZFC.Model.SetTheory.Internal.RelationProgram
import YesMetaZFC.Model.SetTheory.Internal.RelationSubset

/-! # 新共同层的全内部分离

任意内部程序先限制到原关系层对象，再在高模型中分离。子集封闭与完整
前驱实现把所得实际分离集回收到同一低层；全程保留原程序和原赋值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rr_layer_d.separation_l {ω c X R c' Y S q Γ H k a T E F n r i f D : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (my : Smdl_d I c' Y S) (map : Smap_d I ω c c' X Y q)
    (layer : Rr_layer_d I Γ Y S H k) (closed : Rr_closed_d I Y S H) (low : Smem_d I a Γ T)
    (hE : M.IsFunctionSpace I E ω Γ) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hf : M.mem f E) (hD : M.mem D Γ) :
    ∃ A, M.mem A Γ ∧ Ssep_d I Γ T E F n r i f D A := by
  obtain ⟨b, hb, bound, hib, _⟩ := sbound_above_l I hZF hω hF hi hi
  obtain ⟨m, G, V, state⟩ := sr_compile_at_l I hZF hω hF hb
  obtain ⟨u, hu, hru⟩ := state.map.2.2 r hr
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω Y
  obtain ⟨g, fg, assign⟩ := smap_assign_exists_l I hZF layer.injection.1 ((hE f).mp hf)
  obtain ⟨h, gh, fh⟩ := senv_update_exists_l I hZF fg hb layer.member
  have hbg := (gh.2 b H).mpr (Or.inl ⟨rfl, rfl⟩)
  have hbi : b ≠ i := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) b (eq.symm ▸ hib)
  have compare x y (hx : M.mem x Γ) (hxy : Rd_entry_d x y k) v w
      (fv : Senv_update_d I f i x v) (hw : Senv_update_d I h i y w) :
      Ssat_d I Γ T E F n r v ↔ Ssat_d I Y S K G m u w := by
    have hy := layer.injection.1.output_mem_of_pairMember hxy
    apply layer.program_l hZF hω low hE hK hF hr hb bound state hru
      ((hE v).mpr (fv.function_l I ((hE f).mp hf) hi hx))
      ((hK w).mpr (hw.function_l I fh hi hy)) ((hw.2 b H).mpr (Or.inr ⟨hbi, hbg⟩))
    intro j z z' hj hjz hzz
    rcases (fv.2 j z).mp hjz with ⟨rfl, rfl⟩ | ⟨hji, hjz⟩
    · exact (hw.2 j z').mpr (Or.inl ⟨rfl, layer.injection.1.1.2 z z' y hzz hxy⟩)
    · have hjb : j ≠ b := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) b (eq ▸ hj)
      exact (hw.2 j z').mpr (Or.inr ⟨hji, (gh.2 j z').mpr
        (Or.inr ⟨hjb, assign j (hω.transitive hZF b hb j hj) z z' hjz hzz⟩)⟩)
  obtain ⟨d, hd, hDd⟩ := layer.injection.1.2.2 D hD
  obtain ⟨A, hA, sep⟩ := sc_separation_raw_l I hZF hω hX mx my map theory
    hK state.program hu hi ((hK h).mpr fh) hd
  obtain ⟨B, hB, hBA, _⟩ := rr_capture_l I closed layer.transitive layer.injection
    layer.image layer.predecessors hDd hA (fun x hx hxa => ((sep x hx).mp hxa).1)
  have member t z (htz : Rd_entry_d t z k) x y (hxy : Rd_entry_d x y k) :
      M.mem x t ↔ Rd_entry_d y z S :=
    ⟨fun hx => (layer.predecessors t z htz y).mpr ⟨x, hx, hxy⟩, fun hy => by
      obtain ⟨v, hv, hvy⟩ := (layer.predecessors t z htz y).mp hy
      exact layer.injection.2 v x y hvy hxy ▸ hv⟩
  have spec x (hx : M.mem x Γ) :
      M.mem x B ↔ M.mem x D ∧ ∃ v, Senv_update_d I f i x v ∧ Ssat_d I Γ T E F n r v := by
    obtain ⟨y, hy, hxy⟩ := layer.injection.1.2.2 x hx
    have truth :
        (∃ v, Senv_update_d I f i x v ∧ Ssat_d I Γ T E F n r v) ↔
        ∃ w, Senv_update_d I h i y w ∧ Ssat_d I Y S K G m u w := by
      constructor
      · rintro ⟨v, fv, valid⟩
        obtain ⟨w, hw, _⟩ := senv_update_exists_l I hZF fh hi hy
        exact ⟨w, hw, (compare x y hx hxy v w fv hw).mp valid⟩
      · rintro ⟨w, hw, valid⟩
        obtain ⟨v, fv, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
        exact ⟨v, fv, (compare x y hx hxy v w fv hw).mpr valid⟩
    exact (member B A hBA x y hxy).trans
      ((sep y hy).trans (and_congr (member D d hDd x y hxy).symm truth.symm))
  exact ⟨B, hB, fun x => ⟨fun hx => (spec x (layer.transitive B hB x hx)).mp hx,
    fun hx => (spec x (layer.transitive D hD x hx.1)).mpr hx⟩⟩

end YesMetaZFC.SetTheory.Internal
