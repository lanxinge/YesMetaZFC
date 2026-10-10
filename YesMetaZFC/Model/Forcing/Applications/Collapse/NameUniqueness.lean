import YesMetaZFC.Model.Forcing.Applications.Collapse.Names

/-! # 塌缩后继名称的字面唯一性

两份完整规格在任意泛型中给出同一条件集、关系和顶。原 ZF 有效性将其转成
全局等号力迫；规范名称固定点随后给出字面相等，供确定超限递归使用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem collapse_names_unique_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {w X Y A T t A' T' t'}
    (hw : Name_d M B w) (hX : Name_d M B X) (hY : Name_d M B Y)
    (h : Coll_names_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z w X Y A T t)
    (h' : Coll_names_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z w X Y A' T' t') :
    A = A' ∧ T = T' ∧ t = t' := by
  let el : Fin 6 → Term 9 := Fin.cases (.bound 3) (Fin.cases (.bound 4) (Fin.cases (.bound 5)
    (Fin.cases (.bound 6) (Fin.cases (.bound 7) (fun _ => .bound 8)))))
  let er : Fin 6 → Term 9 := Fin.cases .newest (Fin.cases (.bound 1) (Fin.cases (.bound 2)
    (Fin.cases (.bound 6) (Fin.cases (.bound 7) (fun _ => .bound 8)))))
  have hel : ∀ i, (el i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  have her : ∀ i, (er i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  let β : Formula 1 9 := .conj (Formula.extensionalEq (.bound 4) (.bound 1))
    (.conj (Formula.extensionalEq (.bound 5) (.bound 2)) (Formula.extensionalEq (.bound 3) .newest))
  let φ : Formula 1 9 := .imp (coll_names_body_m.bind el) (.imp (coll_names_body_m.bind er) β)
  have hβ : β.FreeClosed := by simp -implicitDefEqProofs [β, Definitional.Formula.FreeClosed]
  have hφ : φ.FreeClosed := by
    simp only [φ, Definitional.Formula.FreeClosed]
    exact ⟨(Definitional.Formula.freeClosed_bind_iff_of_closed _ hel _).mpr coll_names_body_closed_l,
      (Definitional.Formula.freeClosed_bind_iff_of_closed _ her _).mpr coll_names_body_closed_l, hβ⟩
  have valid (N : SetTheory.Structure.{u}) (hN : N.Models ZF) (η : Env N 9) : Formula.satisfies η φ := by
    simp only [φ, Formula.satisfies_imp_iff, Formula.satisfies_bind]
    intro hl hr
    simp only [coll_names_body_m, Formula.satisfies_conj_iff, Formula.satisfies_bind] at hl hr
    let J := kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))
    have hs := (coll_spec_sat_l J hN.1 _ _ _ _ _ _).mp hl.1
    have hs' := (coll_spec_sat_l J hN.1 _ _ _ _ _ _).mp hr.1
    change Coll_spec_d J (η.bound 8) (η.bound 7) (η.bound 6) (η.bound 4) (η.bound 5) at hs
    change Coll_spec_d J (η.bound 8) (η.bound 7) (η.bound 6) (η.bound 1) (η.bound 2) at hs'
    obtain ⟨hQ, hT⟩ := coll_spec_unique_l J hN.1 hs hs'
    have ht := (top_sat_l hN.1 _ _ _ _).mp hl.2.2.1
    have ht' := (top_sat_l hN.1 _ _ _ _).mp hr.2.2.1
    change (N.mem (η.bound 3) (η.bound 4) ∧ ∀ p, N.mem p (η.bound 4) → Entry_d N p (η.bound 3) (η.bound 5)) at ht
    change (N.mem (η.bound 0) (η.bound 1) ∧ ∀ p, N.mem p (η.bound 1) → Entry_d N p (η.bound 0) (η.bound 2)) at ht'
    rw [← hQ, ← hT] at ht'
    have ho := coll_spec_top_unique_l J hN.1 hs ht ht'
    simp only [β, Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hN.1]
    exact ⟨hQ, hT, ho⟩
  let ρ : Env M 9 := (((coll_names_env_l w X Y A T t).push T').push A').push t'
  have hn : ∀ s : Term 9, Name_d M B (s.eval ρ) := by
    intro s
    cases s with
    | free _ => exact hw
    | bound i => exact Fin.cases h'.1.2.2 (Fin.cases h'.1.1 (Fin.cases h'.1.2.1
        (Fin.cases h.1.2.2 (Fin.cases h.1.1 (Fin.cases h.1.2.1 (Fin.cases hY (Fin.cases hX (fun _ => hw)))))))) i
  have both p (hp : M.mem p B) (hz : p ≠ z) :
      Eq_force_d M B R z p A A' ∧ Eq_force_d M B R z p T T' ∧ Eq_force_d M B R z p t t' := by
    have hleft := (forces_bind_l hZF.1 coll_names_body_m el ρ p).mpr
      ((forces_env_l hZF.1 _ coll_names_body_closed_l (coll_names_env_l w X Y A T t) (Definitional.Env.substitute ρ el)
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))) p).mp (h.2.2 p hp hz))
    have hright := (forces_bind_l hZF.1 coll_names_body_m er ρ p).mpr
      ((forces_env_l hZF.1 _ coll_names_body_closed_l (coll_names_env_l w X Y A' T' t') (Definitional.Env.substitute ρ er)
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))) p).mp (h'.2.2 p hp hz))
    have hi := forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hn).1 (forces_regular_l O hZF _ ρ hn) hp hz
      (forces_zf_valid_l O hZF φ hφ valid ρ (fun i => hn (.bound i)) hp hz) hleft
    have he := forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hn).1 (forces_regular_l O hZF β ρ hn) hp hz hi hright
    obtain ⟨hA, hT, ht⟩ := (forces_conj_l _ _ _ p).mp he |>.imp_right fun h => (forces_conj_l _ _ _ p).mp h
    exact ⟨(code_eq_l M hZF.1 B R z _ _ ρ p).mp hA, (code_eq_l M hZF.1 B R z _ _ ρ p).mp hT,
      (code_eq_l M hZF.1 B R z _ _ ρ p).mp ht⟩
  exact ⟨norm_name_congr_l O hZF h.1.1 h'.1.1 (fun p hp hz => (both p hp hz).1)
      (h.2.1 A (Or.inl rfl)) (h'.2.1 A' (Or.inl rfl)),
    norm_name_congr_l O hZF h.1.2.1 h'.1.2.1 (fun p hp hz => (both p hp hz).2.1)
      (h.2.1 T (Or.inr (Or.inl rfl))) (h'.2.1 T' (Or.inr (Or.inl rfl))),
    norm_name_congr_l O hZF h.1.2.2 h'.1.2.2 (fun p hp hz => (both p hp hz).2.2)
      (h.2.1 t (Or.inr (Or.inr rfl))) (h'.2.1 t' (Or.inr (Or.inr rfl)))⟩

end YesMetaZFC.Model.Forcing.Internal
