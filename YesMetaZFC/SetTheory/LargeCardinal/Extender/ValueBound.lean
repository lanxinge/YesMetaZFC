import YesMetaZFC.SetTheory.LargeCardinal.Extender.TupleValue
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SetCode

/-! # 同一代表的有界真值在两次施加之间一致

同一扩展器读同一个源内真值集。有限幂子集一致性搬运这个集合，
两侧源内 Łoś 随即给出实际坍塌值之间的有界公式一致性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_value_agree_l (hZFC : M.Models ZFC)
    {ω κ K K' L X R Y R' F J O Z A p T V q c C W d N S e
      J' O' Z' A' p' T' V' q' c' C' W' d' N' S' e' n D a U : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (source' : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (h' : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L Y R' F J' O' Z' A' p' T' V')
    (limit' : Di_limit_d A' p' T' V' q' C' W')
    (model' : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c' C' W')
    (hN' : M.TransitiveSet N') (target' : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d' N' S')
    (he' : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c' d' C' N' e')
    (haJ : M.mem a J) (haJ' : M.mem a J') (hn : M.mem n ω) (ha : Fn0_d n L a)
    (hD : Ep_space_d κ n D) (haU : Rd_entry_d a U F)
    {k} (φ : Formula 1 k) (hφ : φ.FreeClosed) (hd : φ.IsDelta0) (f : Fin k → M.Domain) (ρ η : Env M k)
    (values : ∀ i, Ep_value_d q e a (f i) (ρ.bound i))
    (values' : ∀ i, Ep_value_d q' e' a (f i) (η.bound i)) : Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  let hZF := ZFC.models_zf_l hZFC
  have left := ep_delta_value_l hZFC source family coherent h limit model hN target he haJ ha hD haU φ hφ hd f ρ values
  have right := ep_delta_value_l hZFC source' (family.transfer_l agree) (coherent.transfer_l hZF agree)
    h' limit' model' hN' target' he' haJ' ha hD haU φ hφ hd f η values'
  apply left.trans (Iff.trans ?_ right.symm)
  constructor <;> rintro ⟨B, hb, hu, sub, hs⟩
  · exact ⟨B, (agree n D B hn hD sub).mp hb, hu, sub, hs⟩
  · exact ⟨B, (agree n D B hn hD sub).mpr hb, hu, sub, hs⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 后继中的有限幂子集具有处处有界的源内代表

对 A⊆μᵐ 读有界 Łoś，界代表的逐点值包含于 κ，因此原代表几乎处处
是 κᵐ 的子集。既容许坐标界，也容许常值 κ；逐点取交保留同一坍塌值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ep_subspace_m {d} (m μ A : Term d) : Formula 1 d :=
  Formula.forallMem A (fn0_m m.weaken μ.weaken .newest)
derive_free_closed ep_subspace_m

theorem ep_subspace_delta_l {d} (m μ A : Term d) : (ep_subspace_m m μ A).IsDelta0 :=
  .forallMem _ (fn0_delta_l ..)

theorem ep_subspace_sat_l (hE : Extensional M) {d} (ρ : Env M d) (m μ A : Term d) :
    Formula.satisfies ρ (ep_subspace_m m μ A) ↔
      ∀ t, M.mem t (A.eval ρ) → Fn0_d (m.eval ρ) (μ.eval ρ) t := by
  simp only [ep_subspace_m, Formula.satisfies_forallMem_iff, fn0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ep_value_bound_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T V q c C W d N S e n m D E a f u μ B : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (haJ : M.mem a J) (hn : M.mem n ω) (hm : M.mem m ω)
    (ha : Fn0_d n L a) (hD : Ep_space_d κ n D) (hE : Ep_space_d κ m E)
    (hfX : M.mem f X) (hf : Fn0_d D X f) (fv : Ep_value_d q e a f B)
    (hu : Fn0_d D X u) (small : ∀ s x, Rd_entry_d s x u → M.MemberSubset x κ) (uv : Ep_value_d q e a u μ)
    (bound : ∀ t, M.mem t B → Fn0_d m μ t) :
    ∃ g, M.mem g X ∧ Fn0_d D X g ∧ (∀ s x, Rd_entry_d s x g → M.MemberSubset x E) ∧ Ep_value_d q e a g B := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨U, haU⟩ := family.total n a hn ha
  have ultra := family.at_l hZF.1 haU ha hD
  obtain ⟨b, j, code, hj, constants⟩ := ep_value_constants_l hZFC source family coherent h limit model he haJ ha hD
  obtain ⟨v, _, _, vc, vv⟩ := constants m m
    (hj.natural_l hZF source.omega source.transitive hN code target source.omega_mem m hm)
  have los := ep_delta_value_l hZFC source family coherent h limit model hN target he haJ ha hD haU (k := 3)
    (ep_subspace_m (.bound 2) (.bound 1) (.bound 0)) (by simp -implicitDefEqProofs) (ep_subspace_delta_l ..)
    (Fin.cases f (Fin.cases u (fun _ => v))) ⟨Fin.cases B (Fin.cases μ (fun _ => m)), fun _ => m⟩
    (Fin.cases fv (Fin.cases uv (fun _ => vv)))
  obtain ⟨H, _, hHU, sub, good⟩ := los.mp ((ep_subspace_sat_l hZF.1 ..).mpr bound)
  obtain ⟨g, hgX, hg, gb, eq⟩ := rs_cap_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hn hD) (source.space_mem_l hZF hm hE) hfX hf ultra.base.bounds ⟨H, hHU, fun s x hs hsx => by
      obtain ⟨y, _, hsy⟩ := hu.2.1 s (sub s hs)
      have point := (ep_subspace_sat_l hZF.1 ..).mp (good s hs
        ⟨Fin.cases x (Fin.cases y (fun _ => m)), fun _ => m⟩ (Fin.cases hsx (Fin.cases hsy (fun _ => vc s (sub s hs)))))
      exact fun t ht => (hE t).mpr ((point t ht).mono_target_l (small s y hsy))⟩
  obtain ⟨H', _, gv⟩ := ep_repr_exists_l hZF family h limit haJ ha hD hgX hg
  obtain ⟨H, fh, hHB⟩ := fv
  exact ⟨g, hgX, hg, gb, H', gv, (ep_repr_atoms_l hZF family h limit haU fh gv).1.mpr eq ▸ hHB⟩

end YesMetaZFC.SetTheory.LargeCardinal
