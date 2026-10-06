import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRelationCode

/-! # 源内乘积沿有限列编号

把两个坐标的已有编号放在同一有限列的零、一位置，再用源内有限列编号。
全过程产生实际源内单射；字母表只要求是包含 ω 的序数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_product_index_l {ω κ K X R A B D f g : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hA : M.mem A X) (hB : M.mem B X) (hD : M.mem D X)
    (product : M.IsCartesianProduct I D A B) (hf : M.mem f X) (hg : M.mem g X)
    (fi : Sc_index_d κ A f) (gi : Sc_index_d κ B g) :
    ∃ e, M.mem e X ∧ M.IsSetInjectionFromTo I e D κ := by
  obtain ⟨q, hq, qi⟩ := source.finite_index_l hZF fi.ordinal
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨o, ho, hoω⟩ := source.omega.1.2 z hzω
  obtain ⟨n, hn, hnω⟩ := source.omega.1.2 o hoω
  have hzo : z ≠ o := by intro eq; subst o; exact hz z ho.predecessor_mem
  obtain ⟨c, code⟩ := source.code
  let ρ : Env M 9 := ⟨Fin.cases A (Fin.cases B (Fin.cases f (Fin.cases g
    (Fin.cases κ (Fin.cases z (Fin.cases o (Fin.cases K (fun _ => q)))))))), fun _ => ω⟩
  let φ : BinarySchema 9 := { body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
    (Formula.existsMem (.bound 8) (Formula.existsMem (.bound 9) (Formula.existsMem (.bound 13)
      (.conj (kpair0_m (.bound 6) (.bound 4) (.bound 3))
        (.conj (rd_entry0_m (.bound 4) (.bound 2) (.bound 9))
          (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 10))
            (.conj (rd_entry0_m (.bound 12) (.bound 2) .newest)
              (.conj (rd_entry0_m (.bound 13) (.bound 1) .newest)
                (rd_entry0_m .newest (.bound 5) (.bound 15))))))))))) }
  have read u i : φ.denote ρ u i ↔ ∃ a, M.mem a A ∧ ∃ b, M.mem b B ∧
      ∃ x, M.mem x κ ∧ ∃ y, M.mem y κ ∧ ∃ s, M.mem s K ∧ KPair_d M u a b ∧
        Rd_entry_d a x f ∧ Rd_entry_d b y g ∧ Rd_entry_d z x s ∧ Rd_entry_d o y s ∧ Rd_entry_d s i q := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨e, he, fn, select⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory φ
    (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (kpair0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..)
        (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))))) ρ
    (Fin.cases hA (Fin.cases hB (Fin.cases hf (Fin.cases hg (Fin.cases source.cardinal_mem
      (Fin.cases (source.transitive ω source.omega_mem z hzω) (Fin.cases (source.transitive ω source.omega_mem o hoω)
        (Fin.cases source.finite_mem (fun _ => hq))))))))) hD source.cardinal_mem (fun u hu => by
      obtain ⟨a, ha, b, hb, pair⟩ := (product u).mp hu
      obtain ⟨x, hx, hax⟩ := fi.total a ha
      obtain ⟨y, hy, hby⟩ := gi.total b hb
      obtain ⟨s, sf, sz, so⟩ := ep_two_values_l hZF hzo ((hn z).mpr (Or.inl ho.predecessor_mem)) hn.predecessor_mem hx hy
      have hs := (source.finite s).mpr ⟨n, hnω, fn0_function_l (ZF.modelsKP hZF) sf⟩
      obtain ⟨i, hi, hsi⟩ := qi.1.2.2 s hs
      exact ⟨i, hi, (read u i).mpr ⟨a, ha, b, hb, x, hx, y, hy, s, hs, pair, hax, hby, sz, so, hsi⟩⟩)
  refine ⟨e, he, fn0_function_l (ZF.modelsKP hZF) fn, fun u v i hu hv => ?_⟩
  obtain ⟨a, ha, b, hb, x, hx, y, hy, s, hs, up, hax, hby, sz, so, hsi⟩ := (read u i).mp (select u i hu)
  obtain ⟨a', ha', b', hb', x', hx', y', hy', s', hs', vp, hax', hby', sz', so', hsi'⟩ := (read v i).mp (select v i hv)
  have eq := qi.2 s s' i hsi hsi'
  subst s'
  obtain ⟨_, _, sf⟩ := (source.finite s).mp hs
  have ex := sf.1.2 z x x' sz sz'
  have ey := sf.1.2 o y y' so so'
  have ea := fi.injective a ha a' ha' x hx hax (ex.symm ▸ hax')
  have eb := gi.injective b hb b' hb' y hy hby (ey.symm ▸ hby')
  exact kpair_unique_l M hZF.1 up (ea.symm ▸ eb.symm ▸ vp)

end YesMetaZFC.SetTheory.LargeCardinal
