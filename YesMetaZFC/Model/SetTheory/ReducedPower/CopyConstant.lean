import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize
import YesMetaZFC.Model.SetTheory.Source.Transport
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull

/-! # 常值代表在源映射下的实际保持 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 常值方程随完整初等图搬运，覆盖目标定义域的全部新成员。 -/
theorem rf_constant_image_l {ω c d X R Y S π D D' x x' f f' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y π) (ext : Rf_ext_d I X R)
    (hD : Rd_entry_d D D' π) (hx : Rd_entry_d x x' π) (hf : Rd_entry_d f f' π)
    (constant : ∀ v, M.mem v X → Rd_entry_d v D R → Rf_val_d I X R v x f) :
    ∀ v, M.mem v Y → Rd_entry_d v D' S → Rf_val_d I Y S v x' f' := by
  have ext' : Rf_ext_d I Y S := map.extensional_l hZF hω mx my ext
  have ex := ext.native_l I mx.2.1
  have ey := ext'.native_l I my.2.1
  let d₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨D, map.1.1.input_mem_of_pairMember hD⟩
  let d₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨D', map.1.1.output_mem_of_pairMember hD⟩
  let x₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨x, map.1.1.input_mem_of_pairMember hx⟩
  let x₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨x', map.1.1.output_mem_of_pairMember hx⟩
  let f₀ : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨f, map.1.1.input_mem_of_pairMember hf⟩
  let f₁ : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨f', map.1.1.output_mem_of_pairMember hf⟩
  let φ : Formula 1 3 := Formula.forallMem (.bound 2) (rd_entry0_m .newest (.bound 2) (.bound 1))
  let ρ : Env (smdl_structure_l I (R := R) mx.2.1) 3 := ⟨Fin.cases f₀ (Fin.cases x₀ (fun _ => d₀)), fun _ => d₀⟩
  let η : Env (smdl_structure_l I (R := S) my.2.1) 3 := ⟨Fin.cases f₁ (Fin.cases x₁ (fun _ => d₁)), fun _ => d₁⟩
  have moved := smap_source_l I hZF hω mx my map φ (by simp -implicitDefEqProofs [φ]) ρ η
    (Fin.cases hf (Fin.cases hx (fun _ => hD)))
  simp only [φ, Formula.satisfies_forallMem_iff, rd_entry0_sat_l ex, rd_entry0_sat_l ey] at moved
  have next := moved.mp (fun v hv => (rf_val_native_l I mx.2.1 ex v x₀ f₀).mp (constant v.val v.property hv))
  exact fun v hv hd => (rf_val_native_l I my.2.1 ey ⟨v, hv⟩ x₁ f₁).mpr (next ⟨v, hv⟩ hd)

/-- 实际常值代表的复制仍是相应值的常值代表。 -/
theorem Rc_copy_d.constant_l {ω c a X R Y S π D E d e t u x x' g g' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I a Y S)
    (map : Smap_d I ω c a X Y π) (ext : Rf_ext_d I X R)
    (hd : Rd_entry_d d e π) (hx : Rd_entry_d x x' π) (ft : Fn0_d D X t) (fu : Fn0_d E Y u)
    (onto : ∀ v, Rd_entry_d v d R → ∃ s, Rd_entry_d s v t)
    (domain : ∀ s v, Rd_entry_d s v u → Rd_entry_d v e S)
    (copy : Rc_copy_d I X R d t Y S u π g g') (constant : Rs_const_d D x g) : Rs_const_d E x' g' := by
  obtain ⟨f, f', _, graph, hff, graph'⟩ := copy
  have values v (_ : M.mem v X) (hv : Rd_entry_d v d R) : Rf_val_d I X R v x f := by
    obtain ⟨s, hsv⟩ := onto v hv
    exact (graph s v x hsv).mp (constant s (ft.bound_l hsv).1)
  have next := rf_constant_image_l hZF hω mx my map ext hd hx hff values
  intro s hs
  obtain ⟨v, hv, hsv⟩ := fu.2.1 s hs
  exact (graph' s v x' hsv).mpr (next v hv (domain s v hsv))

theorem rs_constant_image_l {ω c d X R Y S π D D' x x' f f' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (hD : Rd_entry_d D D' π) (hx : Rd_entry_d x x' π) (hf : Rd_entry_d f f' π)
    (constant : Rs_const_d D x f) : Rs_const_d D' x' f' := by
  have next := rf_constant_image_l hZF hω hm.1 hn.1 hπ (rf_ext_mem_l I hZF.1 hX hm) hD hx hf
    (fun v _ hv => (rf_val_mem_l I hZF.1 hX hm (hπ.1.1.input_mem_of_pairMember hf)).mpr
      (constant v ((hm.2 v D).mp hv).2.2))
  intro v hv
  have hy := hY D' (hπ.1.1.output_mem_of_pairMember hD) v hv
  exact (rf_val_mem_l I hZF.1 hY hn (hπ.1.1.output_mem_of_pairMember hf)).mp
    (next v hy ((hn.2 v D').mpr ⟨hy, hπ.1.1.output_mem_of_pairMember hD, hv⟩))

end YesMetaZFC.SetTheory.Internal
