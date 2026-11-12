import YesMetaZFC.Model.SetTheory.Relations.Hierarchy
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Embedding.Theory

/-! # 原关系秩证书的编码与实际表示读取 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem rr_rank_truth_l {X R a V : M.Domain} : Rr_rank_d I X R a V ↔
    Rr_truth_d I X R (v_sigma_m (.bound 1) .newest) (Fin.cases V (fun _ : Fin 1 => a)) := by
  constructor
  · rintro ⟨ha, hv, h⟩
    refine ⟨Fin.cases hv (fun _ => ha), ?_⟩
    exact (Formula.closed_env_l (v_sigma_m (.bound 1) .newest) (by simp -implicitDefEqProofs)
      (funext (Fin.cases (Subtype.ext rfl) (fun _ => Subtype.ext rfl)))).mp h
  · rintro ⟨h, valid⟩
    refine ⟨h 1, h 0, ?_⟩
    exact (Formula.closed_env_l (v_sigma_m (.bound 1) .newest) (by simp -implicitDefEqProofs)
      (funext (Fin.cases (Subtype.ext rfl) (fun _ => Subtype.ext rfl)))).mp valid

def rr_rank_m {d} (X R a V : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) (v_sigma_m (.bound 1) .newest) X R (Fin.cases V (fun _ : Fin 1 => a))

@[simp] theorem rr_rank_closed_l {d} (X R a V : Term d)
    (hx : X.freeSupport = []) (hr : R.freeSupport = []) (ha : a.freeSupport = []) (hv : V.freeSupport = []) :
    (rr_rank_m X R a V).FreeClosed :=
  rr_truth_closed_l _ (by simp -implicitDefEqProofs) X R _ hx hr (Fin.cases hv (fun _ => ha))

theorem rr_rank_sat_l {d} (ρ : Env M d) (X R a V : Term d) :
    Formula.satisfies ρ (rr_rank_m X R a V) ↔ Rr_rank_d I (X.eval ρ) (R.eval ρ) (a.eval ρ) (V.eval ρ) := by
  let v : Fin 2 → Term d := Fin.cases V (fun _ => a)
  have read := rr_truth_sat_l I ρ (v_sigma_m (.bound 1) .newest) (by simp -implicitDefEqProofs) X R v
  have eq : (fun i => (v i).eval ρ) =
      Fin.cases (V.eval ρ) (fun _ : Fin 1 => a.eval ρ) := funext (Fin.cases rfl (fun _ => rfl))
  rw [eq] at read
  exact read.trans (rr_rank_truth_l I).symm

theorem rr_rank_native_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (hN : (smdl_structure_l I (R := R) nx).Models KP)
    (a V : (smdl_structure_l I (R := R) nx).Domain) :
    Rr_rank_d I X R a.val V.val ↔ V_d (kp_pair_l hN) a V := by
  rw [rr_rank_truth_l]
  let v : Fin 2 → (smdl_structure_l I (R := R) nx).Domain := Fin.cases V (fun _ => a)
  have read := rr_truth_native_l I nx (v_sigma_m (.bound 1) .newest)
    (by simp -implicitDefEqProofs) v
  have eq : (fun i => (v i).val) =
      Fin.cases V.val (fun _ : Fin 1 => a.val) := funext (Fin.cases rfl (fun _ => rfl))
  rw [eq] at read
  exact read.trans (v_sigma_sat_l hN _ (.bound 1) .newest)

theorem rr_rank_mem_l (hKP : M.Models KP) {c X R a V : M.Domain}
    (model : Smem_d I c X R) (trans : M.TransitiveSet X) (ha : M.mem a X) (hv : M.mem V X) :
    Rr_rank_d I X R a V ↔ Vr_d X a V := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨a, ha⟩⟩
  let ρ : Env (rt_model_l X nx) 2 := ⟨Fin.cases ⟨V, hv⟩ (fun _ => ⟨a, ha⟩), fun _ => ⟨a, ha⟩⟩
  have eq : Rr_rank_d I X R a V ↔ Formula.satisfies ρ (v_sigma_m (.bound 1) .newest) := by
    constructor
    · rintro ⟨_, _, h⟩
      exact (smem_formula_l I model nx _ ρ).mpr h
    · intro h
      exact ⟨ha, hv, (smem_formula_l I model nx _ ρ).mp h⟩
  exact eq.trans (vr_sat_l hKP trans nx ρ (.bound 1) .newest)

end YesMetaZFC.SetTheory.Internal

/-! ## 原生极限秩段沿指定嵌入的工作像 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.rank_image_l {ω c X R a A S π : M.Domain}
    (map : Smap_d I ω c a X A π) (hω : M.IsOmega ω)
    (mx : Smdl_d I c X R) (ma : Smem_d I a A S) (trans : M.TransitiveSet A)
    (hX : (smdl_structure_l I (R := R) mx.2.1).Models KP)
    (δ V : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (rank : V_d (kp_pair_l hX) δ V)
    (limit : (smdl_structure_l I (R := R) mx.2.1).IsLimitOrdinal δ) :
    ∃ η W, Rd_entry_d δ.val η π ∧ Rd_entry_d V.val W π ∧
      M.mem W A ∧ Vr_d A η W ∧ M.IsLimitOrdinal η := by
  obtain ⟨η,hη,dη⟩ := map.1.1.2.2 δ.val δ.property
  obtain ⟨W,hW,vW⟩ := map.1.1.2.2 V.val V.property
  have r := (rr_rank_mem_l I (ZF.modelsKP hZF) ma trans hη hW).mp
    ((rr_rank_truth_l I).mpr (((rr_rank_truth_l I).mp
      ((rr_rank_native_l I mx.2.1 hX δ V).mpr rank)).map_l I hZF hω mx ma.1 map
        (by simp -implicitDefEqProofs) (Fin.cases vW (fun _ => dη))))
  have raw := (rr_truth_native_l I mx.2.1 (KP.limit0_m .newest)
    (by simp -implicitDefEqProofs) (fun _ : Fin 1 => δ)).mpr
      ((KP.limit0_sat_l hX _ .newest).mpr limit)
  have moved := raw.map_l I hZF hω mx ma.1 map
    (by simp -implicitDefEqProofs) (fun _ : Fin 1 => dη)
  have limit' := (KP.limit0_sat_l (ZF.modelsKP hZF) _ .newest).mp
    ((rr_truth_mem_l I trans ma (KP.limit0_m .newest) (KP.limit0_delta_l ..) (fun _ : Fin 1 => η)).mp moved).2
  exact ⟨η,W,dη,vW,hW,r,limit'⟩

end YesMetaZFC.SetTheory.Internal
