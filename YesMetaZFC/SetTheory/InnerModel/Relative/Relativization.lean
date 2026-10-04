import YesMetaZFC.SetTheory.InnerModel.Relative.Structure
import YesMetaZFC.Model.SetTheory.LevyReflection.Relativization

/-! # 原公式在相对 J 并类中的统一相对化 -/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}}

def la_rel_m : {n d : Nat} → Formula 1 n → Term d → (Fin n → Term d) → Formula 1 d
  | _, _, .falsum, _, _ => .falsum
  | _, _, .truth, _, _ => .truth
  | _, _, .mem s t, _, e => .mem (s.bind e) (t.bind e)
  | _, _, .atom r hr ts, _, e => .atom r hr (ts.bind e)
  | _, _, .neg φ, A, e => .neg (la_rel_m φ A e)
  | _, _, .conj φ ψ, A, e => .conj (la_rel_m φ A e) (la_rel_m ψ A e)
  | _, _, .disj φ ψ, A, e => .disj (la_rel_m φ A e) (la_rel_m ψ A e)
  | _, _, .imp φ ψ, A, e => .imp (la_rel_m φ A e) (la_rel_m ψ A e)
  | _, _, .iff φ ψ, A, e => .iff (la_rel_m φ A e) (la_rel_m ψ A e)
  | _, _, .existsE φ, A, e => .existsE (.conj (la_m A.weaken .newest)
      (la_rel_m φ A.weaken (Fin.cases .newest (fun i => (e i).weaken))))
  | _, _, .forallE φ, A, e => .forallE (.imp (la_m A.weaken .newest)
      (la_rel_m φ A.weaken (Fin.cases .newest (fun i => (e i).weaken))))

@[simp] theorem la_rel_closed_l {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (A : Term d) (e : Fin n → Term d) (hA : A.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) :
    (la_rel_m φ A e).FreeClosed := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [la_rel_m, Definitional.Formula.FreeClosed]
  case mem s t =>
    simp only [la_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨(Definitional.Term.freeSupport_bind_of_closed e he s).trans hφ.1,
      (Definitional.Term.freeSupport_bind_of_closed e he t).trans hφ.2⟩
  case atom _ _ ts =>
    simp only [la_rel_m, Definitional.Formula.FreeClosed]
    exact (Definitional.TermVector.freeClosed_bind_iff_of_closed e he ts).mpr hφ
  case neg φ ih =>
    simp only [la_rel_m, Definitional.Formula.FreeClosed]
    exact ih hφ A e hA he
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [la_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨ih hφ.1 A e hA he, jh hφ.2 A e hA he⟩
  case existsE φ ih | forallE φ ih =>
    simp only [la_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨la_m_freeClosed A.weaken .newest (by simpa using hA) rfl,
      ih hφ A.weaken _ (by simpa using hA) (Fin.cases rfl (fun i => by simpa using he i))⟩

private theorem la_bind_sat_l (hM : M.Models KPi) (A : M.Domain) (hA : M.TransitiveSet A) {n d}
    (φ : Formula 1 n) (hφ : φ.FreeClosed) (hδ : φ.IsDelta0) (η : Env (la_model_l A hM) n)
    (ρ : Env M d) (e : Fin n → Term d) (he : ∀ i, (e i).eval ρ = (η.bound i).val) :
    Formula.satisfies ρ (φ.bind e) ↔ Formula.satisfies η φ := by
  rw [Formula.satisfies_bind]
  exact (lr_env_congr_l φ hφ _ (image_env_l Subtype.val η) he).trans (la_model_delta_l A hM hA hδ η).symm

theorem la_rel_sat_l (hM : M.Models KPi) (A : M.Domain) (hA : M.TransitiveSet A) {n d}
    (φ : Formula 1 n) (hφ : φ.FreeClosed) (η : Env (la_model_l A hM) n)
    (ρ : Env M d) (T : Term d) (e : Fin n → Term d) (hT : T.eval ρ = A)
    (he : ∀ i, (e i).eval ρ = (η.bound i).val) :
    Formula.satisfies ρ (la_rel_m φ T e) ↔ Formula.satisfies η φ := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [la_rel_m, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff]
  case mem s t =>
    exact la_bind_sat_l hM A hA (.mem s t)
      (by simpa only [Definitional.Formula.FreeClosed] using hφ) (.mem _ _) η ρ e he
  case atom r hr ts =>
    exact la_bind_sat_l hM A hA (.atom r hr ts)
      (by simpa only [Definitional.Formula.FreeClosed] using hφ) (.atom _ _ _) η ρ e he
  case neg φ ih => simpa only [la_rel_m, Formula.satisfies_neg_iff] using not_congr (ih hφ η ρ T e hT he)
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [la_rel_m, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, ih hφ.1 η ρ T e hT he, jh hφ.2 η ρ T e hT he]
  case existsE φ ih | forallE φ ih =>
    have tr (x : (la_model_l A hM).Domain) := ih hφ (η.push x) (ρ.push x.val) T.weaken
      (Fin.cases .newest (fun i => (e i).weaken)) (by simpa using hT)
      (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken ρ x.val (e i)).trans (he i)))
    first
    | simp only [la_rel_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, la_sat_l (KPi.models_iff_l.mp hM).1,
        Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hT]
      exact ⟨fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, (tr ⟨x, hx⟩).mp h⟩,
        fun ⟨x, h⟩ => ⟨x.val, x.property, (tr x).mpr h⟩⟩
    | simp only [la_rel_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, la_sat_l (KPi.models_iff_l.mp hM).1,
        Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hT]
      exact ⟨fun h x => (tr x).mp (h x.val x.property), fun h x hx => (tr ⟨x, hx⟩).mpr (h ⟨x, hx⟩)⟩

end YesMetaZFC.SetTheory.InnerModel.Relative
