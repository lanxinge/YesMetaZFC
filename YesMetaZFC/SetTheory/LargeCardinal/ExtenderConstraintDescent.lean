import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceConstraints
import YesMetaZFC.SetTheory.LargeCardinal.JointFiber
import YesMetaZFC.SetTheory.Collapse.RelationSequence

/-! # 共同纤维把下降代表列变成实际下降值列

节点保留原代表函数；同一个单射支撑列使节点的求值唯一。逐边约束的共同
实现因而通过唯一值替代形成整张下降图，无须另选各节点的求值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Eb_eval_d (ω κ L e h u x : M.Domain) : Prop :=
  ∃ a f r, KPair_d M u a f ∧ Ec_eval_d ω κ L e h a r ∧ Rd_entry_d r x f

def eb_eval_m {d} (ω κ L e h u x : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.conj (kpair0_m (w u) (.bound 2) (.bound 1))
    (.conj (ec_eval_m (w ω) (w κ) (w L) (w e) (w h) (.bound 2) .newest) (rd_entry0_m .newest (w x) (.bound 1))))))
derive_free_closed eb_eval_m

theorem eb_eval_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L e h u x : Term d) :
    Formula.satisfies ρ (eb_eval_m ω κ L e h u x) ↔
      Eb_eval_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (e.eval ρ) (h.eval ρ) (u.eval ρ) (x.eval ρ) := by
  simp only [eb_eval_m, Eb_eval_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, ec_eval_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Eb_witness_d.realize_l (hKP : M.Models KP) {ω κ L B J K V R F G u v c E e h s : M.Domain}
    (witness : Eb_witness_d ω κ L B J K V R F G u v c E)
    (fe : Fn0_d ω L e) (fh : Fn0_d ω κ h) (hs : M.mem s E) (eval : Ec_eval_d ω κ L e h c s) :
    ∃ x y, M.mem x B ∧ M.mem y B ∧ Eb_eval_d ω κ L e h u x ∧ Eb_eval_d ω κ L e h v y ∧ Rd_entry_d x y R := by
  obtain ⟨a, _, f, _, b, _, g, _, up, vp, _, _, _, _, m, _, n, _, l, _, r, _, t, _, fr, ft, fc, ca, cb, point⟩ := witness
  obtain ⟨p, _, q, _, x, hx, y, hy, cp, cq, px, qy, xy⟩ := point s hs
  exact ⟨x, y, hx, hy, ⟨a, f, p, up, ec_eval_comp_l hKP fe fh fc fr ca cp eval, px⟩,
    ⟨b, g, q, vp, ec_eval_comp_l hKP fe fh fc ft cb cq eval, qy⟩, xy⟩

theorem Eb_pool_d.eval_unique_l (hKP : M.Models KP) {ω κ L X B J K P G D e h u x y : M.Domain}
    (pool : Eb_pool_d ω κ L X B J K P G D) (hu : M.mem u D)
    (injective : ∀ i j x, Rd_entry_d i x e → Rd_entry_d j x e → i = j) (fh : Fn0_d ω κ h)
    (hx : Eb_eval_d ω κ L e h u x) (hy : Eb_eval_d ω κ L e h u y) : x = y := by
  obtain ⟨a, _, f, _, pair, _, _, A, _, _, _, fn⟩ := (pool.nodes u).mp hu
  obtain ⟨a', f', r, pair', er, hrx⟩ := hx
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair pair'
  obtain ⟨a', f', s, pair', es, hsy⟩ := hy
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair pair'
  have eq := ec_eval_unique_l hKP.1 injective fh es er
  subst s
  exact (fn0_function_l hKP fn).1.2 r x y hrx hsy

/-- 每条边的同一纤维约束给出一条背景内部下降列，适用于任意被观察关系。 -/
theorem eb_desc_realize_l (hZF : M.Models ZF) {ω κ L X B J K P G D V R F s A C Q e h : M.Domain}
    (hω : M.IsOmega ω) (pool : Eb_pool_d ω κ L X B J K P G D) (fn : Fn0_d ω D s)
    (fa : Fn0_d ω J A) (fc : Fn0_d ω Q C) (fe : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) e ω L)
    (fh : Fn0_d ω κ h)
    (realize : ∀ i c E, Rd_entry_d i c A → Rd_entry_d i E C → ∃ r, M.mem r E ∧ Ec_eval_d ω κ L e h c r)
    (constraints : ∀ i j u v c E, M.SuccessorOf j i → Rd_entry_d i u s → Rd_entry_d j v s →
      Rd_entry_d i c A → Rd_entry_d i E C → Eb_witness_d ω κ L B J K V R F G v u c E) :
    ∃ v, Fn0_d ω B v ∧ Wf_desc_d R v := by
  have edge i j u v (hji : M.SuccessorOf j i) (hiu : Rd_entry_d i u s) (hjv : Rd_entry_d j v s) :
      ∃ x y, M.mem x B ∧ M.mem y B ∧ Eb_eval_d ω κ L e h v x ∧ Eb_eval_d ω κ L e h u y ∧ Rd_entry_d x y R := by
    obtain ⟨c, _, hic⟩ := fa.2.1 i (fn.bound_l hiu).1
    obtain ⟨E, _, hiE⟩ := fc.2.1 i (fn.bound_l hiu).1
    obtain ⟨r, hr, er⟩ := realize i c E hic hiE
    exact (constraints i j u v c E hji hiu hjv hic hiE).realize_l (ZF.modelsKP hZF)
      (fn0_of_function_l (ZF.modelsKP hZF) fe.1) fh hr er
  let ρ : Env M 8 := ⟨Fin.cases s (Fin.cases D (Fin.cases B (Fin.cases e (Fin.cases h
    (Fin.cases L (Fin.cases κ (fun _ => ω))))))), fun _ => ω⟩
  let φ : BinarySchema 8 := {
    body := Formula.existsMem (.bound 3)
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 3)) (.conj (.mem (.bound 1) (.bound 5))
        (eb_eval_m (.bound 10) (.bound 9) (.bound 8) (.bound 6) (.bound 7) .newest (.bound 1)))) }
  have sat i x : φ.denote ρ i x ↔ ∃ u, M.mem u D ∧ Rd_entry_d i u s ∧ M.mem x B ∧ Eb_eval_d ω κ L e h u x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff, eb_eval_sat_l hZF.1]; rfl
  obtain ⟨v, vf, values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ (source := ω) (target := B)
    (fun i hi => by
      obtain ⟨j, hji, hj⟩ := hω.1.2 i hi
      obtain ⟨u, hu, hiu⟩ := fn.2.1 i hi
      obtain ⟨v, _, hjv⟩ := fn.2.1 j hj
      obtain ⟨_, x, _, hx, _, ex, _⟩ := edge i j u v hji hiu hjv
      exact ⟨x, (sat i x).mpr ⟨u, hu, hiu, hx, ex⟩⟩)
    (fun i _ x y hx hy => by
      obtain ⟨u, hu, hiu, _, ex⟩ := (sat i x).mp hx
      obtain ⟨v, _, hiv, _, ey⟩ := (sat i y).mp hy
      have eq := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 i v u hiv hiu
      subst v
      exact pool.eval_unique_l (ZF.modelsKP hZF) hu fe.2 fh ex ey)
    (fun i x _ hx => ((sat i x).mp hx).elim fun _ h => h.2.2.1)
  refine ⟨v, fn0_of_function_l (ZF.modelsKP hZF) vf, fun i j x y hji hix hjy => ?_⟩
  obtain ⟨u, hu, hiu, _, ex⟩ := (sat i x).mp ((values i x).mp hix).2
  obtain ⟨w, hw, hjw, _, ey⟩ := (sat j y).mp ((values j y).mp hjy).2
  obtain ⟨y', x', _, _, ey', ex', rel⟩ := edge i j u w hji hiu hjw
  have eqx := pool.eval_unique_l (ZF.modelsKP hZF) hu fe.2 fh ex' ex
  have eqy := pool.eval_unique_l (ZF.modelsKP hZF) hw fe.2 fh ey' ey
  exact eqx ▸ eqy ▸ rel

end YesMetaZFC.SetTheory.LargeCardinal
