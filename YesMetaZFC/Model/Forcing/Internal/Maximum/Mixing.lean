import YesMetaZFC.Model.Forcing.Internal.Forcing.Congruence

/-! # 任意内部预序上的名称混合

由实际公式选择的名称族可以沿条件拼合。重叠选择只需在共同加强上被迫使相等；
混合结论同样是局部等号力迫，不依赖某个已经选定的泛型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

/-- 在条件交叠处相容的可定义名称选择具有实际混合名称。 -/
theorem mixing_l {n} (φ : BinarySchema n) (ρ : Env M n) {W} (hW : Supp_d M B W)
    (hc : ∀ p q s t r, M.mem p B → M.mem q B → M.mem s W → M.mem t W →
      φ.denote ρ s p → φ.denote ρ t q → Below_d M B R z r p → Below_d M B R z r q →
      Eq_force_d M B R z r s t) :
    ∃ u, Name_d M B u ∧
      (∀ a d, Entry_d M a d u → ∃ s b, M.mem s W ∧ Entry_d M a b s) ∧
      ∀ p s, M.mem p B → M.mem s W → φ.denote ρ s p → Eq_force_d M B R z p u s := by
  let δ := (((ρ.push B).push R).push z).push W
  let e : Fin n → Term (n+9) := fun i => .bound ⟨i.val+9, by omega⟩
  let ψ : BinarySchema (n+4) := {
    body := .existsE (.existsE (.existsE
      (.conj (.mem (.bound 2) (.bound 5)) (.conj (.mem (.bound 1) (.bound 8))
        (.conj (binary_pred_m φ e (.bound 2) (.bound 1))
          (.conj (below_m (.bound 8) (.bound 7) (.bound 6) (.bound 3) (.bound 1))
            (.conj (entry_m (.bound 4) .newest (.bound 2)) (entry_m (.bound 3) .newest (.bound 7)))))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, e] }
  have hψ a d : ψ.denote δ a d ↔ ∃ t p b,
      M.mem t W ∧ M.mem p B ∧ φ.denote ρ t p ∧ Below_d M B R z d p ∧
        Entry_d M a b t ∧ Entry_d M d b R := by
    have he t p b : (⟨fun i => (e i).eval (((((δ.push a).push d).push t).push p).push b),
        (((((δ.push a).push d).push t).push p).push b).free⟩ : Env M n) = ρ := by cases ρ; rfl
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, binary_pred_sat_l, below_sat_l M hZF.1, entry_sat_l M hZF.1, he]
    rfl
  obtain ⟨u, hu, _, hU⟩ := name_comp_l M hZF ψ δ B W (fun a ha => ⟨W, ha, hW⟩)
  have bound a d (had : Entry_d M a d u) : ∃ s b, M.mem s W ∧ Entry_d M a b s := by
    obtain ⟨s, _, b, hs, _, _, _, hab, _⟩ := (hψ a d).mp ((hU a d).mp had).2.2
    exact ⟨s, b, hs, hab⟩
  refine ⟨u, hu, bound, fun p t hp ht hφ => ?_⟩
  have htN : Name_d M B t := ⟨W, ht, hW⟩
  apply (eq_force_unfold_l M hZF hu htN).mpr
  refine ⟨hp, ?_, ?_⟩
  · intro a d had q hq hqd
    obtain ⟨_, hdB, hψ'⟩ := (hU a d).mp had
    obtain ⟨s, r, b, hs, hrB, hsr, hdr, hab, hdb⟩ := (hψ a d).mp hψ'
    have hbB := (supp_entry_l M hW hs hab).2
    have hqr := below_trans_l O hrB ⟨hq.1, hq.2.1, hqd⟩ hdr
    have hqb := O.trans q d b hq.1 hdB hbB hqd hdb
    have he := hc r p s t q hrB hp hs ht hsr hφ hqr hq
    have hl := (eq_force_unfold_l M hZF ⟨W, hs, hW⟩ htN).mp he |>.2.1
    exact hl a b hab q (below_refl_l O hq.1 hq.2.1) hqb
  · intro a b hab q hq hqb
    have ha := (supp_entry_l M hW ht hab).1
    refine ⟨q, a, q, below_refl_l O hq.1 hq.2.1, ?_, O.refl q hq.1,
      eq_force_refl_l O hZF hq.1 ⟨W, ha, hW⟩⟩
    exact (hU a q).mpr ⟨ha, hq.1, (hψ a q).mpr ⟨t, p, b, ht, hp, hφ, hq, hab, hqb⟩⟩

end YesMetaZFC.Model.Forcing.Internal
