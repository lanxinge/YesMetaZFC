import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Step
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.Model.SetTheory.Relations.RecordImage

/-! # 所属短扩展器与不可达性的外层公式

显式参数所属条件与原公式的有界相对化精确对应已有的所属判断。
原生子模型公式仍在各自背景中解释；通过实际隶属关系码读取所属证书。
树边另用原关系相对化，语义解码不要求传递源。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ex_local_m {d} (ω κ L X F : Term d) : Formula 1 d :=
  .conj (.mem ω X) (.conj (.mem κ X) (.conj (.mem L X) (.conj (.mem F X)
    (lr_rel_m (ex_short_m (.bound 3) (.bound 2) (.bound 1) (.newest : Term 4)) X
      (Fin.cases F (Fin.cases L (Fin.cases κ (fun _ => ω))))))))

@[simp] theorem ex_local_closed_l {d} (ω κ L X F : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hl : L.freeSupport = [])
    (hx : X.freeSupport = []) (hf : F.freeSupport = []) : (ex_local_m ω κ L X F).FreeClosed := by
  simp only [ex_local_m, Definitional.Formula.FreeClosed, hw, hk, hl, hx, hf, true_and]
  exact lr_rel_closed_l _ (ex_short_m_freeClosed _ _ _ _ rfl rfl rfl rfl) X _ hx
    (Fin.cases hf (Fin.cases hl (Fin.cases hk (fun _ => hw))))

theorem ex_local_delta_l {d} (ω κ L X F : Term d) : (ex_local_m ω κ L X F).IsDelta0 :=
  .conj (.mem ..) (.conj (.mem ..) (.conj (.mem ..) (.conj (.mem ..) (lr_rel_delta_l ..))))

/-- 树边在所属模型的原关系中检验同一个短扩展器公式。 -/
def it_local_m {d} (ω X R κ L F : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) (n := 3)
    (ex_short_m (.bound 3) (.bound 2) (.bound 1) (.bound 0)) X R
    (Fin.cases F (Fin.cases L (Fin.cases κ (fun _ => ω))))

@[simp] theorem it_local_closed_l {d} (ω X R κ L F : Term d)
    (hw : ω.freeSupport = []) (hx : X.freeSupport = []) (hr : R.freeSupport = [])
    (hk : κ.freeSupport = []) (hl : L.freeSupport = []) (hf : F.freeSupport = []) :
    (it_local_m ω X R κ L F).FreeClosed :=
  rr_truth_closed_l _ (ex_short_m_freeClosed _ _ _ _ rfl rfl rfl rfl) X R _ hx hr
    (Fin.cases hf (Fin.cases hl (Fin.cases hk (fun _ => hw))))

theorem it_local_sat_l (I : kpair_convention_l.Interpretation M) {d} (ρ : Env M d)
    (ω X R κ L F : Term d) : Formula.satisfies ρ (it_local_m ω X R κ L F) ↔
      It_local_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  rw [it_local_m, rr_truth_sat_l I ρ _ (ex_short_m_freeClosed _ _ _ _ rfl rfl rfl rfl)]
  constructor
  · rintro ⟨h, valid⟩
    refine ⟨h 3, h 2, h 1, h 0, ?_⟩
    exact (Formula.closed_env_l _ (ex_short_m_freeClosed _ _ _ _ rfl rfl rfl rfl)
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))).mp valid
  · rintro ⟨hw, hk, hl, hf, valid⟩
    refine ⟨Fin.cases hf (Fin.cases hl (Fin.cases hk (fun _ => hw))), ?_⟩
    exact (Formula.closed_env_l _ (ex_short_m_freeClosed _ _ _ _ rfl rfl rfl rfl)
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))).mp valid

def ex_inaccessible_m {d} (ω X L : Term d) : Formula 1 d := .conj (.mem ω X) (.conj (.mem L X)
  (lr_rel_m (sc_inaccessible_m (.bound 1) (.newest : Term 2)) X (Fin.cases L (fun _ => ω))))

@[simp] theorem ex_inaccessible_closed_l {d} (ω X L : Term d)
    (hw : ω.freeSupport = []) (hx : X.freeSupport = []) (hl : L.freeSupport = []) :
    (ex_inaccessible_m ω X L).FreeClosed := by
  simp only [ex_inaccessible_m, Definitional.Formula.FreeClosed, hw, hx, hl, true_and]
  exact lr_rel_closed_l _ (sc_inaccessible_m_freeClosed _ _ rfl rfl) X _ hx (Fin.cases hl (fun _ => hw))

theorem ex_inaccessible_delta_l {d} (ω X L : Term d) : (ex_inaccessible_m ω X L).IsDelta0 :=
  .conj (.mem ..) (.conj (.mem ..) (lr_rel_delta_l ..))

theorem ex_local_sat_l (I : kpair_convention_l.Interpretation M) {R : M.Domain} {d}
    (ρ : Env M d) (ω κ L X F : Term d) (hX : M.TransitiveSet (X.eval ρ))
    (code : ∃ c, Smem_d I c (X.eval ρ) R) :
    Formula.satisfies ρ (ex_local_m ω κ L X F) ↔ It_local_d I (ω.eval ρ) (X.eval ρ) R (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  rw [it_local_mem_l I code]
  have read (hw : M.mem (ω.eval ρ) (X.eval ρ)) (hk : M.mem (κ.eval ρ) (X.eval ρ))
      (hl : M.mem (L.eval ρ) (X.eval ρ)) (hf : M.mem (F.eval ρ) (X.eval ρ)) :
      Formula.satisfies ρ (lr_rel_m (ex_short_m (.bound 3) (.bound 2) (.bound 1) (.newest : Term 4)) X
        (Fin.cases F (Fin.cases L (Fin.cases κ (fun _ => ω))))) ↔
      Formula.satisfies (⟨Fin.cases ⟨F.eval ρ, hf⟩ (Fin.cases ⟨L.eval ρ, hl⟩
        (Fin.cases ⟨κ.eval ρ, hk⟩ (fun _ => ⟨ω.eval ρ, hw⟩))), fun _ => ⟨ω.eval ρ, hw⟩⟩ :
        Env (rt_model_l (X.eval ρ) ⟨⟨ω.eval ρ, hw⟩⟩) 4) (ex_short_m (.bound 3) (.bound 2) (.bound 1) .newest) := by
    let η : Env (rt_model_l (X.eval ρ) ⟨⟨ω.eval ρ, hw⟩⟩) 4 :=
      ⟨Fin.cases ⟨F.eval ρ, hf⟩ (Fin.cases ⟨L.eval ρ, hl⟩ (Fin.cases ⟨κ.eval ρ, hk⟩ (fun _ => ⟨ω.eval ρ, hw⟩))),
        fun _ => ⟨ω.eval ρ, hw⟩⟩
    exact sc_relative_sat_l hX ⟨⟨ω.eval ρ, hw⟩⟩
      (ex_short_m (.bound 3) (.bound 2) (.bound 1) .newest) (ex_short_m_freeClosed _ _ _ _ rfl rfl rfl rfl)
      η ρ X (Fin.cases F (Fin.cases L (Fin.cases κ (fun _ => ω)))) rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))
  simp only [ex_local_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
  exact ⟨fun ⟨hw, hk, hl, hf, h⟩ => ⟨hw, hk, hl, hf, (read hw hk hl hf).mp h⟩,
    fun ⟨hw, hk, hl, hf, h⟩ => ⟨hw, hk, hl, hf, (read hw hk hl hf).mpr h⟩⟩

theorem ex_inaccessible_sat_l {d} (ρ : Env M d) (ω X L : Term d) (hX : M.TransitiveSet (X.eval ρ)) :
    Formula.satisfies ρ (ex_inaccessible_m ω X L) ↔ Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (L.eval ρ) := by
  have read (hw : M.mem (ω.eval ρ) (X.eval ρ)) (hl : M.mem (L.eval ρ) (X.eval ρ)) :
      Formula.satisfies ρ (lr_rel_m (sc_inaccessible_m (.bound 1) (.newest : Term 2)) X (Fin.cases L (fun _ => ω))) ↔
      Formula.satisfies (⟨Fin.cases ⟨L.eval ρ, hl⟩ (fun _ => ⟨ω.eval ρ, hw⟩), fun _ => ⟨ω.eval ρ, hw⟩⟩ :
        Env (rt_model_l (X.eval ρ) ⟨⟨ω.eval ρ, hw⟩⟩) 2) (sc_inaccessible_m (.bound 1) .newest) := by
    let η : Env (rt_model_l (X.eval ρ) ⟨⟨ω.eval ρ, hw⟩⟩) 2 :=
      ⟨Fin.cases ⟨L.eval ρ, hl⟩ (fun _ => ⟨ω.eval ρ, hw⟩), fun _ => ⟨ω.eval ρ, hw⟩⟩
    exact sc_relative_sat_l hX ⟨⟨ω.eval ρ, hw⟩⟩
      (sc_inaccessible_m (.bound 1) .newest) (sc_inaccessible_m_freeClosed _ _ rfl rfl)
      η ρ X (Fin.cases L (fun _ => ω)) rfl (Fin.cases rfl (fun _ => rfl))
  simp only [ex_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
  exact ⟨fun ⟨hw, hl, h⟩ => ⟨hw, hl, (read hw hl).mp h⟩, fun ⟨hw, hl, h⟩ => ⟨hw, hl, (read hw hl).mpr h⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
