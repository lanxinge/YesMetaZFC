import YesMetaZFC.Model.Forcing.Applications.Collapse.NameUniqueness

/-! # 规范塌缩名称三元组的原公式

公式保留全部名称性、规范固定点与全局规格力迫，确定规则直接使用该已实现关系。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def coll_names_m {n} (B R z w X Y A T t : Term n) : Formula 1 n :=
  .conj (.conj (name_m B A) (.conj (name_m B T) (name_m B t)))
    (.conj (.conj (norm_name_m B R z A A) (.conj (norm_name_m B R z T T) (norm_name_m B R z t t)))
      (force_all_m coll_names_body_m (Fin.cases t (Fin.cases A (Fin.cases T (Fin.cases Y (Fin.cases X (fun _ => w)))))) B R z))

@[simp] theorem coll_names_closed_l {n} (B R z w X Y A T t : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = []) (hw : w.freeSupport = [])
    (hX : X.freeSupport = []) (hY : Y.freeSupport = []) (hA : A.freeSupport = []) (hT : T.freeSupport = []) (ht : t.freeSupport = []) :
    (coll_names_m B R z w X Y A T t).FreeClosed := by
  simp only [coll_names_m, Definitional.Formula.FreeClosed]
  exact ⟨⟨name_m_freeClosed _ _ hB hA, name_m_freeClosed _ _ hB hT, name_m_freeClosed _ _ hB ht⟩,
    ⟨norm_name_closed_l _ _ _ _ _ hB hR hz hA hA, norm_name_closed_l _ _ _ _ _ hB hR hz hT hT,
      norm_name_closed_l _ _ _ _ _ hB hR hz ht ht⟩,
    force_all_closed_l _ _ _ _ _ coll_names_body_closed_l
      (Fin.cases ht (Fin.cases hA (Fin.cases hT (Fin.cases hY (Fin.cases hX (fun _ => hw)))))) hB hR hz⟩

theorem coll_names_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (B R z w X Y A T t : Term n) : Formula.satisfies ρ (coll_names_m B R z w X Y A T t) ↔
      Coll_names_d I (B.eval ρ) (R.eval ρ) (z.eval ρ) (w.eval ρ) (X.eval ρ) (Y.eval ρ) (A.eval ρ) (T.eval ρ) (t.eval ρ) := by
  simp only [coll_names_m, Formula.satisfies_conj_iff, name_sat_l M hE, norm_name_sat_l M I hE, force_all_sat_l hE]
  let e : Fin 6 → Term n := Fin.cases t (Fin.cases A (Fin.cases T (Fin.cases Y (Fin.cases X (fun _ => w)))))
  have he p := forces_env_l (B := B.eval ρ) (R := R.eval ρ) (z := z.eval ρ) hE coll_names_body_m coll_names_body_closed_l
    (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M 6)
    (coll_names_env_l (w.eval ρ) (X.eval ρ) (Y.eval ρ) (A.eval ρ) (T.eval ρ) (t.eval ρ))
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))) p
  simp only [e] at he
  simp only [he]
  exact ⟨fun h => ⟨h.1, fun s hs => hs.elim (fun e => e.symm ▸ h.2.1.1)
      (fun hs => hs.elim (fun e => e.symm ▸ h.2.1.2.1) (fun e => e.symm ▸ h.2.1.2.2)), h.2.2⟩,
    fun h => ⟨h.1, ⟨h.2.1 _ (Or.inl rfl), h.2.1 _ (Or.inr (Or.inl rfl)), h.2.1 _ (Or.inr (Or.inr rfl))⟩, h.2.2⟩⟩

end YesMetaZFC.Model.Forcing.Internal
