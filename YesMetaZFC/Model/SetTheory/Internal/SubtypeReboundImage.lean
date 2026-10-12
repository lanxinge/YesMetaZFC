import YesMetaZFC.Model.SetTheory.Internal.SubtypeRebound
import YesMetaZFC.Model.SetTheory.Internal.TypePoolImage

/-! # 子类型定义域更换的实际初等像

完整类型先满足统一的有界更换性质，再整体搬运到目标中的全部查询。
原投影查询的成员性本身保证它的常量属于像域，无须假设一个额外的秩覆盖。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.rebound_l {ω c d X R Y S j n b z U N E D t U' N' E' D' t' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j) (hωX : M.mem ω X)
    {σ : Fin 7 → M.Domain} (hnω : M.mem n ω) (hb : M.mem b ω) (hz : M.mem z ω) (hσ : ∀ i, M.mem (σ i) ω)
    (hu : Rd_entry_d U U' j) (hN : Rd_entry_d N N' j) (hE : Rd_entry_d E E' j)
    (hD : Rd_entry_d D D' j) (ht : Rd_entry_d t t' j) :
    Ts_rebound_d ω n b z U N E D t σ ↔ Ts_rebound_d ω n b z U' N' E' D' t' σ := by
  let ρ (U N E D t : M.Domain) : Env M 16 := ⟨Fin.cases t (Fin.cases D (Fin.cases E (Fin.cases N
    (Fin.cases U (Fin.cases z (Fin.cases b (Fin.cases n (Fin.cases ω σ)))))))), fun _ => ω⟩
  let slots : Fin 7 → Term 16 := fun i => .bound ⟨i.val + 9, by omega⟩
  let φ : Formula 1 16 := ts_rebound_m (.bound 8) (.bound 7) (.bound 6) (.bound 5)
    (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest slots
  have fixed := hj.natural_l hZF hω hX hY hm hn hωX
  have hw := hj.omega_l I hZF hω hX hY hm hn hωX
  have tr := smap_delta_l I hZF hω hX hY hm hn hj φ
    (by simp -implicitDefEqProofs [φ, slots]) (ts_rebound_delta_l ..) (ρ U N E D t) (ρ U' N' E' D' t')
    (Fin.cases ht (Fin.cases hD (Fin.cases hE (Fin.cases hN (Fin.cases hu (Fin.cases (fixed z hz)
      (Fin.cases (fixed b hb) (Fin.cases (fixed n hnω) (Fin.cases hw (fun i => fixed (σ i) (hσ i)))))))))))
  have read U N E D t : Formula.satisfies (ρ U N E D t) φ ↔ Ts_rebound_d ω n b z U N E D t σ := by
    dsimp only [φ]
    rw [ts_rebound_sat_l (ZF.modelsKP hZF)]
    have eq : (fun i => (slots i).eval (ρ U N E D t)) = σ := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))) i
    exact eq ▸ Iff.rfl
  exact (read U N E D t).symm.trans (tr.trans (read U' N' E' D' t'))

theorem Smap_d.subtype_rebound_l {ω θ X R Y S c d j n b a z U D t U' D' t' η A c₀ R₀ r δ
    κ ξ τ m V w : M.Domain} {σ : Fin 7 → M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (theory : Sc_theory_d I ω Y S)
    (prog : Ts_program_d hZF ω n b σ a z) (hUX : M.mem U X)
    (hU : Rd_entry_d U U' j) (hD : Rd_entry_d D D' j) (ht : Rd_entry_d t t' j)
    (hA : V_d I η A) (model : Smem_d I c₀ A R₀) (type : Tt_realized_d I ω c₀ A R₀ n r δ U D t)
    (hωU : M.mem ω U) (nat : M.MemberSubset ω U)
    (hκ : M.IsLimitOrdinal κ) (hξ : M.IsLimitOrdinal ξ) (hτ : M.IsLimitOrdinal τ)
    (hτξ : M.mem τ ξ) (hξU : M.mem ξ U') (hmm : M.mem m ω)
    (subtype : Ts_subtype_d ω n κ τ m V w b σ z t') : Ts_subtype_d ω n ξ τ m U' w b σ z t' := by
  obtain ⟨N, E, N', E', names, seq, prod, hN, hE, names', seq', prod'⟩ :=
    hj.type_full_l hZF hω hX hθ hωX hY hm hn theory prog.finite hUX hU hD type.pool
  have full : Tt_pool_d I ω n U' D' := ⟨N', E', names', seq', prod'⟩
  have closed := prog.rebound_l hZF hω hA model type names hωU nat (E := E)
  have image := (hj.rebound_l hZF hω (ZF.v_transitive_l I hZF hX) hY hm hn hωX prog.finite prog.length
    (sc_num_natural_l I hZF hω prog.code) (fun i => hω.transitive hZF b prog.length (σ i) (prog.slots i)) hU hN hE hD ht).mp closed
  have sub := (hj.subset_l hZF hω (ZF.v_transitive_l I hZF hX) hY hm hn ht hD).mp
    (fun p hp => ((type.truth p).mp hp).1)
  obtain ⟨hτκ, nm, q, code, hq⟩ := subtype
  have code' := code.pool_l (ZF.modelsKP hZF) (hω.members_areOrdinals hZF n prog.finite) full (sub q hq)
  obtain ⟨q', hq', query⟩ := prog.query_exists_l hZF full
    ⟨code'.constants.1, code'.constants.2.1, code'.constants.2.2.1, code'.constants.2.2.2.1, hξU, code'.constants.2.2.2.2.2⟩
  obtain ⟨C, col, cq⟩ := code'.column_l hZF.1 names'
  obtain ⟨C', col', cq'⟩ := query.column_l hZF.1 names'
  have truth := image κ code'.constants.2.2.2.2.1 ξ hξU τ code'.constants.2.2.2.1 m hmm w code'.constants.1
    ⟨hκ, hξ, hτ, hτκ, hτξ⟩ C ((seq' C).mpr ⟨b, prog.length, fn0_function_l (ZF.modelsKP hZF) col.1⟩) col
    C' ((seq' C').mpr ⟨b, prog.length, fn0_function_l (ZF.modelsKP hZF) col'.1⟩) col' q (sub q hq) q' hq' cq cq'
  exact ⟨hτξ, nm, q', query, truth.mp hq⟩

end YesMetaZFC.SetTheory.Internal
