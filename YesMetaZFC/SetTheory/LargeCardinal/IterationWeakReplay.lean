import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakRun

/-! # 运行的唯一性与前缀重放

唯一性只使用 ZF 和两张已给定图的单值性，不调用集合包络或新的选择。
限制对手走法后，旧运行的相同前缀仍是递归运行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_run_d.unique_l {o Ψ F α Z H K : M.Domain} (hF : M.IsSetFunction I F) (hΨ : M.IsSetFunction I Ψ)
    (h : Wi_run_d hZF o Ψ F α Z H) (k : Wi_run_d hZF o Ψ F α Z K) : H = K := by
  change M.IsRecursiveSequenceIn I (Wi_drive_d o Ψ F) H α Z at h
  change M.IsRecursiveSequenceIn I (Wi_drive_d o Ψ F) K α Z at k
  let η : Env M 3 := ((⟨fun _ => o, fun _ => o⟩ : Env M 1).push Ψ).push F
  have eq : wi_drive_schema.denote η = Wi_drive_d o Ψ F :=
    funext fun H => funext fun s => propext (wi_drive_sat_l (ZF.modelsKP hZF) η H s)
  apply ZF.recursiveSequenceIn_unique hZF I η wi_drive_schema h.1.1 (Or.inl rfl) ?_ (eq.symm ▸ h) (eq.symm ▸ k)
  intro J ⟨_, β, _, seq⟩ x y hx hy
  exact (eq ▸ hx).unique_l (ZF.modelsKP hZF) ⟨seq.1, seq.2.1, seq.2.2.1⟩ hF hΨ (eq ▸ hy)

theorem Wi_run_d.restrict_moves_l {o Ψ F Ω Z R α H F' : M.Domain} (run : Wi_run_d hZF o Ψ F Ω Z R)
    (hi : M.mem α Ω) (rh : M.IsRestrictionOf I H R α) (rf : M.IsRestrictionOf I F' F α) :
    Wi_run_d hZF o Ψ F' α Z H := by
  have part := run.restriction hi rh
  refine ⟨part.1, fun i hi s hs => ?_⟩
  obtain ⟨J, rj, β, t, r, u, B, dom, input, request, edge, pair⟩ := part.2 i hi s hs
  have seq := part.restriction hi rj
  have eq := Structure.IsDomainOf.eq (𝕀 := I) hZF.1 dom seq.1.2.2.1
  subst β
  refine ⟨J, rj, i, t, r, u, B, dom, ?_, request, edge, pair⟩
  exact input.elim (fun ⟨ξ, next, ht⟩ => Or.inl ⟨ξ, next, (rf.2 ξ t).mpr
    ⟨part.1.1.transitive i hi ξ next.predecessor_mem, ht⟩⟩) Or.inr

def wi_run_m {d} (o Ψ F α Z H : Term d) : Formula 1 d :=
  Formula.isRecursiveSequenceIn kpair_convention_l wi_drive_schema
    (Definitional.TermVector.ofFn (Fin.cases F (Fin.cases Ψ (fun _ => o)))) H α Z

@[simp] theorem wi_run_closed_l {d} (o Ψ F α Z H : Term d) (ho : o.freeSupport = []) (hp : Ψ.freeSupport = [])
    (hf : F.freeSupport = []) (hα : α.freeSupport = []) (hz : Z.freeSupport = []) (hh : H.freeSupport = []) :
    (wi_run_m o Ψ F α Z H).FreeClosed := by
  have he : (Definitional.TermVector.ofFn (Fin.cases F (Fin.cases Ψ (fun _ : Fin 1 => o)))).FreeClosed := by
    intro i
    cases i using Fin.cases with
    | zero => exact hf
    | succ i => cases i using Fin.cases with
      | zero => exact hp
      | succ i => simpa only [Definitional.TermVector.get_ofFn, Fin.cases_succ] using ho
  exact Formula.isRecursiveSequenceIn_freeClosed _ _ _ _ _ _ he hh hα hz

theorem wi_run_sat_l {d} (η : Env M d) (o Ψ F α Z H : Term d) :
    Formula.satisfies η (wi_run_m o Ψ F α Z H) ↔
      Wi_run_d hZF (o.eval η) (Ψ.eval η) (F.eval η) (α.eval η) (Z.eval η) (H.eval η) := by
  rw [wi_run_m, Formula.satisfies_isRecursiveSequenceIn_iff I hZF.1]
  refine and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi =>
    forall_congr' fun s => imp_congr_right fun hs => exists_congr fun J => and_congr_right fun _ => ?_
  exact wi_drive_sat_l (ZF.modelsKP hZF) _ J s

end YesMetaZFC.SetTheory.LargeCardinal
