import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRelationCode
import YesMetaZFC.Model.SetTheory.Internal.SourceCantor

/-! # 源内可数支撑族的源内单射覆盖列

用一项自然数列编码 ω 本身，两项自然数列编码支撑族的逐坐标求值。
已有有限列编号给出像集的源内 ω 编号，再在源内施行 Cantor–Bernstein。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ec_source_cover_l {ω κ K X R L S A : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (hL : M.mem L X) (hωL : M.MemberSubset ω L) (hA : M.mem A X)
    (seq : Fseq_space_d I ω L S) (fn : Fn0_d ω S A) : ∃ f, M.mem f X ∧ M.IsSetInjectionFromTo I f ω L ∧
      ∀ i a j x, Rd_entry_d i a A → Rd_entry_d j x a → ∃ n, Rd_entry_d n x f := by
  obtain ⟨c, code⟩ := source.code
  obtain ⟨S', hS', seq'⟩ := source.sequences.space L hL
  have hS : M.mem S X := hZF.1.eq_of_same_members S' S (fun f => (seq' f).trans (seq f).symm) ▸ hS'
  obtain ⟨K₀, small⟩ := source.rebase_l hZF source.omega_mem (fun _ h => h) (source.cardinal_small.mono_l source.below)
  obtain ⟨ι, hι, index⟩ := small.finite_index_l hZF (source.omega.isOrdinal hZF)
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨o, ho, hoω⟩ := source.omega.1.2 z hzω
  obtain ⟨t, ht, htω⟩ := source.omega.1.2 o hoω
  have hzo : z ≠ o := fun eq => hz z (eq ▸ ho.predecessor_mem)
  have hot : o ≠ t := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) o (eq.symm ▸ ht.predecessor_mem)
  let value k x := (Fn0_d o ω k ∧ Rd_entry_d z x k) ∨ (Fn0_d t ω k ∧
    ∃ i, M.mem i ω ∧ ∃ j, M.mem j ω ∧ ∃ a, M.mem a S ∧
      Rd_entry_d z i k ∧ Rd_entry_d o j k ∧ Rd_entry_d i a A ∧ Rd_entry_d j x a)
  have bounded k x (hv : value k x) : M.mem x L := by
    rcases hv with ⟨hk, hx⟩ | ⟨_, _, _, j, _, a, ha, _, _, _, hx⟩
    · exact hωL x (hk.bound_l hx).2
    · obtain ⟨_, _, hf⟩ := (seq a).mp ha
      exact hf.output_mem_of_pairMember hx
  have unique k x y (hx : value k x) (hy : value k y) : x = y := by
    rcases hx with ⟨hk, hzx⟩ | ⟨hk, i, _, j, _, a, ha, hzi, hoj, hia, hjx⟩ <;>
      rcases hy with ⟨hk', hzy⟩ | ⟨hk', i', _, j', _, a', _, hzi', hoj', hia', hjy⟩
    · exact (fn0_function_l (ZF.modelsKP hZF) hk).1.2 z x y hzx hzy
    · exact (hot (hk.domain_eq_l hZF.1 hk')).elim
    · exact (hot (hk'.domain_eq_l hZF.1 hk)).elim
    · have ei := (fn0_function_l (ZF.modelsKP hZF) hk).1.2 z i' i hzi' hzi
      have ej := (fn0_function_l (ZF.modelsKP hZF) hk).1.2 o j' j hoj' hoj
      subst i' j'
      have ea := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 i a' a hia' hia
      subst a'
      obtain ⟨_, _, hf⟩ := (seq a).mp ha
      exact hf.1.2 j x y hjx hjy
  let ρ : Env M 6 := ⟨Fin.cases A (Fin.cases S (Fin.cases t (Fin.cases o (Fin.cases z (fun _ => ω))))), fun _ => ω⟩
  let φ : BinarySchema 6 := {
    body := .disj (.conj (fn0_m (.bound 5) (.bound 7) (.bound 1)) (rd_entry0_m (.bound 6) .newest (.bound 1)))
      (.conj (fn0_m (.bound 4) (.bound 7) (.bound 1)) (Formula.existsMem (.bound 7) (Formula.existsMem (.bound 8)
        (Formula.existsMem (.bound 5) (.conj (rd_entry0_m (.bound 9) (.bound 2) (.bound 4))
          (.conj (rd_entry0_m (.bound 8) (.bound 1) (.bound 4))
            (.conj (rd_entry0_m (.bound 2) .newest (.bound 5)) (rd_entry0_m (.bound 1) (.bound 3) .newest)))))))) }
  have delta : φ.body.IsDelta0 := .disj (.conj (fn0_delta_l ..) (rd_entry0_delta_l ..))
    (.conj (fn0_delta_l ..) (.existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))
  have sat k x : φ.denote ρ k x ↔ value k x := by
    simp only [φ, BinarySchema.denote, value, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_existsMem_iff, fn0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  let e : Fin 8 → Fin 9 := Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ))
  let e' : Fin 8 → Fin 10 := Fin.cases 0 (Fin.cases 2 (fun i => i.succ.succ.succ.succ))
  let η := ρ.push L
  let ψ : BinarySchema 7 := {
    body := .disj (φ.body.rename e) (.conj (.neg (Formula.existsMem (.bound 2) (φ.body.rename e')))
      (Formula.extensionalEq .newest (.bound 7)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have read k x : ψ.denote η k x ↔ value k x ∨ ((¬ ∃ y, M.mem y L ∧ value k y) ∧ x = z) := by
    have point : Formula.satisfies ((η.push k).push x) (φ.body.rename e) ↔ value k x :=
      (Formula.satisfies_rename ..).trans ((Formula.closed_env_l φ.body φ.freeClosed
        (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))).trans (sat k x))
    have point' y : Formula.satisfies (((η.push k).push x).push y) (φ.body.rename e') ↔ value k y :=
      (Formula.satisfies_rename ..).trans ((Formula.closed_env_l φ.body φ.freeClosed
        (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))).trans (sat k y))
    simp only [ψ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_existsMem_iff, point, point', Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨F, hFX, ff, select⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory ψ
    (.disj (delta.rename_l e) (.conj (.neg (.existsMem _ (delta.rename_l e'))) (.atom ..))) η
    (Fin.cases hL (Fin.cases hA (Fin.cases hS (Fin.cases (source.transitive ω source.omega_mem t htω)
      (Fin.cases (source.transitive ω source.omega_mem o hoω) (Fin.cases (source.transitive ω source.omega_mem z hzω)
        (fun _ => source.omega_mem))))))) small.finite_mem hL (fun k _ => by
      classical
      by_cases h : ∃ x, M.mem x L ∧ value k x
      · obtain ⟨x, hx, hv⟩ := h
        exact ⟨x, hx, (read k x).mpr (Or.inl hv)⟩
      · exact ⟨z, hωL z hzω, (read k z).mpr (Or.inr ⟨h, rfl⟩)⟩)
  have realize k x (hk : M.mem k K₀) (hv : value k x) : Rd_entry_d k x F := by
    obtain ⟨y, _, hky⟩ := ff.2.1 k hk
    rcases (read k y).mp (select k y hky) with hy | ⟨no, _⟩
    · exact unique k y x hy hv ▸ hky
    · exact (no ⟨x, bounded k x hv, hv⟩).elim
  obtain ⟨C, hC, range⟩ := sc_range_source_l hZF source.omega source.transitive code source.theory hFX
  have cl x (hx : M.mem x C) : M.mem x L := ((range x).mp hx).elim fun _ h => (ff.bound_l h).2
  have omega x (hx : M.mem x ω) : M.mem x C := by
    obtain ⟨k, _, _, _, kf, kv⟩ := sc_constant_l hZF source.omega source.transitive code source.theory
      (source.transitive ω source.omega_mem o hoω) (source.transitive ω source.omega_mem x hx)
    have kω := kf.retarget_l (fun i y hiy => ((kv i y).mp hiy).2 ▸ hx)
    exact (range x).mpr ⟨k, realize k x ((small.finite k).mpr ⟨o, hoω, fn0_function_l (ZF.modelsKP hZF) kω⟩)
      (Or.inl ⟨kω, (kv z x).mpr ⟨ho.predecessor_mem, rfl⟩⟩)⟩
  have covered i a j x (hia : Rd_entry_d i a A) (hjx : Rd_entry_d j x a) : M.mem x C := by
    obtain ⟨n, hn, ha⟩ := (seq a).mp (fn.bound_l hia).2
    have hi := (fn.bound_l hia).1
    have hj := source.omega.transitive hZF n hn j (ha.input_mem_of_pairMember hjx)
    obtain ⟨k, kf, k0, k1⟩ := ep_two_values_l hZF hzo ((ht z).mpr (Or.inl ho.predecessor_mem)) ht.predecessor_mem hi hj
    exact (range x).mpr ⟨k, realize k x ((small.finite k).mpr ⟨t, htω, fn0_function_l (ZF.modelsKP hZF) kf⟩)
      (Or.inr ⟨kf, i, hi, j, hj, a, (fn.bound_l hia).2, k0, k1, hia, hjx⟩)⟩
  obtain ⟨j, hj, cj⟩ := sc_index_image_l hZF source.omega source.transitive code source.theory small.finite_mem hC hFX
    source.omega_mem hι (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (source.omega.isOrdinal hZF) index)
    (ff.retarget_l (fun k x hkx => (range x).mpr ⟨k, hkx⟩)) (fun x hx => ((range x).mp hx).imp fun k hk => ⟨(ff.bound_l hk).1, hk⟩)
  obtain ⟨j', hj', inj⟩ := cj.restrict_l hZF source.omega source.transitive code source.theory hC source.omega_mem hj
  let equal : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let ε : Env M 0 := ⟨Fin.elim0, fun _ => ω⟩
  have eqs a b : equal.denote ε a b ↔ a = b := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨i, hi, fi, is⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory equal (.atom ..)
    ε (fun k => Fin.elim0 k) source.omega_mem hC (fun x hx => ⟨x, omega x hx, (eqs x x).mpr rfl⟩)
  have ii : M.IsSetInjectionFromTo I i ω C := ⟨fn0_function_l (ZF.modelsKP hZF) fi,
    fun a b x ha hb => ((eqs a x).mp (is a x ha)).trans ((eqs b x).mp (is b x hb)).symm⟩
  obtain ⟨f, hf, bij⟩ := sc_cantor_bernstein_l hZF source.omega source.transitive code source.theory source.omega_mem hC hi hj' ii inj
  exact ⟨f, hf, ⟨bij.1.1.mono_target_l I cl, bij.1.2⟩,
    fun i a j x hia hjx => (bij.2 x (covered i a j x hia hjx)).imp fun _ h => h.2⟩

end YesMetaZFC.SetTheory.LargeCardinal
