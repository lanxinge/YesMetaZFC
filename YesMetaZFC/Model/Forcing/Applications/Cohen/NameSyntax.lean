import YesMetaZFC.Model.Forcing.Applications.Cohen.Presentation
import YesMetaZFC.Model.Forcing.Internal.Maximum.NormalSyntax
import YesMetaZFC.Model.Forcing.TwoStep.Top

/-! # 规范 Cohen 名称的原公式规格

条件集、序关系与顶名称均为规范固定点，且在每个正条件下实现 Cohen 规格。
该关系以实际原公式表达，供内部集合构造与超限递归直接使用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def cohen_env_l (κ A T : M.Domain) : Env M 3 :=
  ((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push T).push A

def Cohen_names_d (I : kpair_convention_l.Interpretation M) (B R z κ A T t : M.Domain) : Prop :=
  (Name_d M B A ∧ Name_d M B T ∧ Name_d M B t) ∧
  (∀ s, s = A ∨ s = T ∨ s = t → Norm_name_d M I B R z s s) ∧
  (∀ p, M.mem p B → p ≠ z →
    Forces_d M B R z (cohen_m (.bound 2) .newest (.bound 1)) (cohen_env_l κ A T) p) ∧
  (∀ p, M.mem p B → p ≠ z →
    Forces_d M B R z (preord_m .newest (.bound 1)) (ord_env_l M A T) p) ∧
  ∀ p, M.mem p B → p ≠ z →
    Forces_d M B R z (top_m (.bound 1) (.bound 2) .newest) (top_env_l A T t) p

def cohen_names_m {n} (B R z κ A T t : Term n) : Formula 1 n :=
  .conj (.conj (name_m B A) (.conj (name_m B T) (name_m B t)))
    (.conj (.conj (norm_name_m B R z A A) (.conj (norm_name_m B R z T T) (norm_name_m B R z t t)))
      (.conj (force_all_m (cohen_m (.bound 2) .newest (.bound 1))
        (fun i : Fin 3 => match i.val with | 0 => A | 1 => T | _ => κ) B R z)
        (.conj (force_all_m (preord_m .newest (.bound 1))
          (fun i : Fin 2 => match i.val with | 0 => A | _ => T) B R z)
          (force_all_m (top_m (.bound 1) (.bound 2) .newest)
            (fun i : Fin 3 => match i.val with | 0 => t | 1 => A | _ => T) B R z))))

@[simp] theorem cohen_names_closed_l {n} (B R z κ A T t : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hκ : κ.freeSupport = []) (hA : A.freeSupport = []) (hT : T.freeSupport = []) (ht : t.freeSupport = []) :
    (cohen_names_m B R z κ A T t).FreeClosed := by
  have hc : ∀ i : Fin 3, (match i.val with | 0 => A | 1 => T | _ => κ).freeSupport = [] := by
    intro i; split <;> assumption
  have hp : ∀ i : Fin 2, (match i.val with | 0 => A | _ => T).freeSupport = [] := by
    intro i; split <;> assumption
  have hm : ∀ i : Fin 3, (match i.val with | 0 => t | 1 => A | _ => T).freeSupport = [] := by
    intro i; split <;> assumption
  simp only [cohen_names_m, Definitional.Formula.FreeClosed]
  exact ⟨⟨name_m_freeClosed _ _ hB hA, name_m_freeClosed _ _ hB hT, name_m_freeClosed _ _ hB ht⟩,
    ⟨norm_name_closed_l _ _ _ _ _ hB hR hz hA hA,
      norm_name_closed_l _ _ _ _ _ hB hR hz hT hT, norm_name_closed_l _ _ _ _ _ hB hR hz ht ht⟩,
    force_all_closed_l _ _ _ _ _ (cohen_m_freeClosed _ _ _ rfl rfl rfl) hc hB hR hz,
    force_all_closed_l _ _ _ _ _ (preord_m_freeClosed _ _ rfl rfl) hp hB hR hz,
    force_all_closed_l _ _ _ _ _ (top_m_freeClosed _ _ _ rfl rfl rfl) hm hB hR hz⟩

theorem cohen_names_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (B R z κ A T t : Term n) : Formula.satisfies ρ (cohen_names_m B R z κ A T t) ↔
      Cohen_names_d I (B.eval ρ) (R.eval ρ) (z.eval ρ) (κ.eval ρ) (A.eval ρ) (T.eval ρ) (t.eval ρ) := by
  simp only [cohen_names_m, Formula.satisfies_conj_iff, name_sat_l M hE, norm_name_sat_l M I hE, force_all_sat_l hE]
  have hc p := forces_env_l (B := B.eval ρ) (R := R.eval ρ) (z := z.eval ρ) hE
    (cohen_m (.bound 2) .newest (.bound 1)) (cohen_m_freeClosed _ _ _ rfl rfl rfl)
    (⟨fun i => (match i.val with | 0 => A | 1 => T | _ => κ).eval ρ, ρ.free⟩ : Env M 3)
    (cohen_env_l (κ.eval ρ) (A.eval ρ) (T.eval ρ))
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) p
  have hp p := forces_env_l (B := B.eval ρ) (R := R.eval ρ) (z := z.eval ρ) hE
    (preord_m .newest (.bound 1)) (preord_m_freeClosed _ _ rfl rfl)
    (⟨fun i => (match i.val with | 0 => A | _ => T).eval ρ, ρ.free⟩ : Env M 2)
    (ord_env_l M (A.eval ρ) (T.eval ρ)) (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) p
  have ht p := forces_env_l (B := B.eval ρ) (R := R.eval ρ) (z := z.eval ρ) hE
    (top_m (.bound 1) (.bound 2) .newest) (top_m_freeClosed _ _ _ rfl rfl rfl)
    (⟨fun i => (match i.val with | 0 => t | 1 => A | _ => T).eval ρ, ρ.free⟩ : Env M 3)
    (top_env_l (A.eval ρ) (T.eval ρ) (t.eval ρ))
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) p
  simp only [hc, hp, ht]
  refine ⟨fun h => ⟨h.1, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, fun h => ?_⟩
  · intro s hs
    exact hs.elim (fun he => he.symm ▸ h.2.1.1)
      (fun hs => hs.elim (fun he => he.symm ▸ h.2.1.2.1) (fun he => he.symm ▸ h.2.1.2.2))
  · exact ⟨h.1, ⟨h.2.1 _ (Or.inl rfl), h.2.1 _ (Or.inr (Or.inl rfl)),
      h.2.1 _ (Or.inr (Or.inr rfl))⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end YesMetaZFC.Model.Forcing.Internal
