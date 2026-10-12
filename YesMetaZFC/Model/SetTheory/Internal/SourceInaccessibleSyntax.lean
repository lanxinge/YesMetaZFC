import YesMetaZFC.Model.SetTheory.Internal.SourceRelative
import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessible

/-! # 内部不可达判断的背景原公式

完整展开定义原子后，相对化适用于任意真实载体；此处不偷加源模型传递性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_inaccessible_raw_m {d} (ω X κ : Term d) : Formula 1 d := .conj (.mem ω X) (.conj (.mem κ X)
  (sr_rel_m (sc_inaccessible_m (.bound 1 : Term 2) .newest) X (Fin.cases κ (fun _ => ω))))

@[simp] theorem sc_inaccessible_raw_closed_l {d} (ω X κ : Term d)
    (hw : ω.freeSupport = []) (hX : X.freeSupport = []) (hk : κ.freeSupport = []) :
    (sc_inaccessible_raw_m ω X κ).FreeClosed := by
  exact ⟨⟨hw, hX⟩, ⟨⟨hk, hX⟩, sr_rel_closed_l _ (sc_inaccessible_m_freeClosed _ _ rfl rfl)
    X _ hX (Fin.cases hk (fun _ => hw))⟩⟩

theorem sc_inaccessible_raw_sat_l {d} (ρ : Env M d) (ω X κ : Term d) :
    Formula.satisfies ρ (sc_inaccessible_raw_m ω X κ) ↔
      Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (κ.eval ρ) := by
  simp only [sc_inaccessible_raw_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Sc_inaccessible_d]
  have read (hw : M.mem (ω.eval ρ) (X.eval ρ)) (hk : M.mem (κ.eval ρ) (X.eval ρ)) :=
    sr_rel_sat_l ⟨⟨ω.eval ρ, hw⟩⟩ (sc_inaccessible_m (.bound 1 : Term 2) .newest)
      (sc_inaccessible_m_freeClosed _ _ rfl rfl)
      ⟨Fin.cases ⟨κ.eval ρ, hk⟩ (fun _ => ⟨ω.eval ρ, hw⟩), fun _ => ⟨ω.eval ρ, hw⟩⟩
      ρ X (Fin.cases κ (fun _ => ω)) rfl (Fin.cases rfl (fun _ => rfl))
  exact ⟨fun ⟨hw, hk, h⟩ => ⟨hw, hk, (read hw hk).mp h⟩,
    fun ⟨hw, hk, h⟩ => ⟨hw, hk, (read hw hk).mpr h⟩⟩

end YesMetaZFC.SetTheory.Internal
