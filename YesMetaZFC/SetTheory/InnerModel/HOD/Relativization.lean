import YesMetaZFC.SetTheory.InnerModel.HOD.Relative

/-! # 原公式在两种遗传参数类中的统一相对化 -/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def ha_rel_m (k : Bool) : {n d : Nat} → Formula 1 n → Term d → (Fin n → Term d) → Formula 1 d
  | _, _, .falsum, _, _ => .falsum
  | _, _, .truth, _, _ => .truth
  | _, _, .mem s t, _, e => .mem (s.bind e) (t.bind e)
  | _, _, .atom r hr ts, _, e => .atom r hr (ts.bind e)
  | _, _, .neg φ, A, e => .neg (ha_rel_m k φ A e)
  | _, _, .conj φ ψ, A, e => .conj (ha_rel_m k φ A e) (ha_rel_m k ψ A e)
  | _, _, .disj φ ψ, A, e => .disj (ha_rel_m k φ A e) (ha_rel_m k ψ A e)
  | _, _, .imp φ ψ, A, e => .imp (ha_rel_m k φ A e) (ha_rel_m k ψ A e)
  | _, _, .iff φ ψ, A, e => .iff (ha_rel_m k φ A e) (ha_rel_m k ψ A e)
  | _, _, .existsE φ, A, e => .existsE (.conj (ha_m k A.weaken .newest)
      (ha_rel_m k φ A.weaken (Fin.cases .newest (fun i => (e i).weaken))))
  | _, _, .forallE φ, A, e => .forallE (.imp (ha_m k A.weaken .newest)
      (ha_rel_m k φ A.weaken (Fin.cases .newest (fun i => (e i).weaken))))

@[simp] theorem ha_rel_closed_l (k : Bool) {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (A : Term d) (e : Fin n → Term d) (hA : A.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) :
    (ha_rel_m k φ A e).FreeClosed := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [ha_rel_m, Definitional.Formula.FreeClosed]
  case mem s t =>
    simp only [ha_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨(Definitional.Term.freeSupport_bind_of_closed e he s).trans hφ.1,
      (Definitional.Term.freeSupport_bind_of_closed e he t).trans hφ.2⟩
  case atom _ _ ts =>
    simp only [ha_rel_m, Definitional.Formula.FreeClosed]
    exact (Definitional.TermVector.freeClosed_bind_iff_of_closed e he ts).mpr hφ
  case neg φ ih =>
    simp only [ha_rel_m, Definitional.Formula.FreeClosed]
    exact ih hφ A e hA he
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [ha_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨ih hφ.1 A e hA he, jh hφ.2 A e hA he⟩
  case existsE φ ih | forallE φ ih =>
    simp only [ha_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨ha_closed_l k A.weaken .newest (by simpa using hA) rfl,
      ih hφ A.weaken _ (by simpa using hA) (Fin.cases rfl (fun i => by simpa using he i))⟩

private theorem ha_bind_sat_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {n d}
    (φ : Formula 1 n) (hφ : φ.FreeClosed) (hδ : φ.IsDelta0) (η : Env (ha_model_l hZF k A) n)
    (ρ : Env M d) (e : Fin n → Term d) (he : ∀ i, (e i).eval ρ = (η.bound i).val) :
    Formula.satisfies ρ (φ.bind e) ↔ Formula.satisfies η φ := by
  rw [Formula.satisfies_bind]
  exact (lr_env_congr_l φ hφ _ (image_env_l Subtype.val η) he).trans (ha_model_delta_l hZF k A hδ η).symm

theorem ha_rel_sat_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {n d}
    (φ : Formula 1 n) (hφ : φ.FreeClosed) (η : Env (ha_model_l hZF k A) n)
    (ρ : Env M d) (T : Term d) (e : Fin n → Term d) (hT : T.eval ρ = A)
    (he : ∀ i, (e i).eval ρ = (η.bound i).val) :
    Formula.satisfies ρ (ha_rel_m k φ T e) ↔ Formula.satisfies η φ := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [ha_rel_m, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff]
  case mem s t =>
    exact ha_bind_sat_l hZF k A (.mem s t)
      (by simpa only [Definitional.Formula.FreeClosed] using hφ) (.mem _ _) η ρ e he
  case atom r hr ts =>
    exact ha_bind_sat_l hZF k A (.atom r hr ts)
      (by simpa only [Definitional.Formula.FreeClosed] using hφ) (.atom _ _ _) η ρ e he
  case neg φ ih => simpa only [ha_rel_m, Formula.satisfies_neg_iff] using not_congr (ih hφ η ρ T e hT he)
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [ha_rel_m, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, ih hφ.1 η ρ T e hT he, jh hφ.2 η ρ T e hT he]
  case existsE φ ih | forallE φ ih =>
    have tr (x : (ha_model_l hZF k A).Domain) := ih hφ (η.push x) (ρ.push x.val) T.weaken
      (Fin.cases .newest (fun i => (e i).weaken)) (by simpa using hT)
      (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken ρ x.val (e i)).trans (he i)))
    first
    | simp only [ha_rel_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, ha_sat_l hZF.1,
        Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hT]
      exact ⟨fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, (tr ⟨x, hx⟩).mp h⟩,
        fun ⟨x, h⟩ => ⟨x.val, x.property, (tr x).mpr h⟩⟩
    | simp only [ha_rel_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, ha_sat_l hZF.1,
        Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hT]
      exact ⟨fun h x => (tr x).mp (h x.val x.property), fun h x hx => (tr ⟨x, hx⟩).mpr (h ⟨x, hx⟩)⟩

end YesMetaZFC.SetTheory.InnerModel
