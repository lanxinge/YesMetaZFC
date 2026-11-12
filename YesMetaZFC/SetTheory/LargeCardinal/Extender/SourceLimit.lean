import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.Model.SetTheory.Source.Relation
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.JointFiber
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraCertificate
import YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedGraph
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed
import YesMetaZFC.SetTheory.CountableChoice
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceJointFiber

/-! # 源内下降代表列的实际测度约束族

逐条边从既有共同支撑证书中选取支撑和测度一集合。选择关系是有界原公式，
值域由支撑集与测度族之并的乘积给出，因此两张可数约束图均留在施加源。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Eb_witness_d (ω κ L B J K V R F G u v c E : M.Domain) : Prop :=
  ∃ a, M.mem a J ∧ ∃ f, M.mem f G ∧ ∃ b, M.mem b J ∧ ∃ g, M.mem g G ∧
    KPair_d M u a f ∧ KPair_d M v b g ∧ ∃ U, M.mem U V ∧ Rd_entry_d c U F ∧
      M.mem E U ∧ Eb_constraint_d ω κ L B K R a f b g c E

def eb_witness_m {d} (ω κ L B J K V R F G u v c E : Term d) : Formula 1 d :=
  let w (x : Term d) := x.weaken.weaken.weaken.weaken
  Formula.existsMem J (Formula.existsMem G.weaken (Formula.existsMem J.weaken.weaken (Formula.existsMem G.weaken.weaken.weaken
    (.conj (kpair0_m (w u) (.bound 3) (.bound 2)) (.conj (kpair0_m (w v) (.bound 1) .newest)
      (Formula.existsMem (w V) (.conj (rd_entry0_m (w c).weaken .newest (w F).weaken)
        (.conj (.mem (w E).weaken .newest) (eb_constraint_m (w ω).weaken (w κ).weaken (w L).weaken (w B).weaken
          (w K).weaken (w R).weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) (w c).weaken (w E).weaken)))))))))
derive_free_closed eb_witness_m

theorem eb_witness_delta_l {d} (ω κ L B J K V R F G u v c E : Term d) :
    (eb_witness_m ω κ L B J K V R F G u v c E).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..)
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (.mem ..) (eb_constraint_delta_l ..)))))))))

theorem eb_witness_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L B J K V R F G u v c E : Term d) :
    Formula.satisfies ρ (eb_witness_m ω κ L B J K V R F G u v c E) ↔
      Eb_witness_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (B.eval ρ) (J.eval ρ) (K.eval ρ) (V.eval ρ)
        (R.eval ρ) (F.eval ρ) (G.eval ρ) (u.eval ρ) (v.eval ρ) (c.eval ρ) (E.eval ρ) := by
  simp only [eb_witness_m, Eb_witness_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, rd_entry0_sat_l hE, Formula.satisfies_mem_iff, eb_constraint_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem eb_source_constraints_l {ω κ K X R₀ L B J G V R F D s : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R₀) (hL : M.mem L X) (hB : M.mem B X)
    (hJ : M.mem J X) (hG : M.mem G X) (hV : M.mem V X) (hR : M.mem R X) (hF : M.mem F X)
    (hD : M.mem D X) (hs : M.mem s X) (fn : Fn0_d ω D s)
    (functional : ∀ a U V, Rd_entry_d a U F → Rd_entry_d a V F → U = V)
    (links : ∀ i j u v, M.SuccessorOf j i → Rd_entry_d i u s → Rd_entry_d j v s → Eb_link_d ω κ L B J K V R F G v u) :
    ∃ P A C, M.mem P X ∧ M.mem A X ∧ M.mem C X ∧ Fn0_d ω J A ∧ Fn0_d ω P C ∧
      (∀ i c E U, Rd_entry_d i c A → Rd_entry_d i E C → Rd_entry_d c U F → M.mem E U) ∧
      ∀ i j u v c E, M.SuccessorOf j i → Rd_entry_d i u s → Rd_entry_d j v s →
        Rd_entry_d i c A → Rd_entry_d i E C → Eb_witness_d ω κ L B J K V R F G v u c E := by
  obtain ⟨code, model⟩ := source.code
  obtain ⟨P, hP, union⟩ := (source.algebra_l (ZF.modelsKP hZF)).union V hV
  obtain ⟨T, hT, product⟩ := (source.algebra_l (ZF.modelsKP hZF)).product J P hJ hP
  let ρ : Env M 13 := ⟨Fin.cases P (Fin.cases s (Fin.cases D (Fin.cases G (Fin.cases F (Fin.cases R (Fin.cases V
    (Fin.cases J (Fin.cases B (Fin.cases L (Fin.cases K (Fin.cases κ (fun _ => ω)))))))))))), fun _ => ω⟩
  let φ : BinarySchema 13 := {
    body := Formula.existsMem (.bound 14) (.conj (KP.succ0_m .newest (.bound 2))
      (Formula.existsMem (.bound 5) (Formula.existsMem (.bound 6)
        (.conj (rd_entry0_m (.bound 4) (.bound 1) (.bound 6)) (.conj (rd_entry0_m (.bound 2) .newest (.bound 6))
          (Formula.existsMem (.bound 12) (Formula.existsMem (.bound 6) (.conj (kpair0_m (.bound 5) (.bound 1) .newest)
            (eb_witness_m (.bound 19) (.bound 18) (.bound 16) (.bound 15) (.bound 14) (.bound 17) (.bound 13)
              (.bound 12) (.bound 11) (.bound 10) (.bound 2) (.bound 3) (.bound 1) .newest))))))))) }
  have sat i p : φ.denote ρ i p ↔ ∃ j, M.mem j ω ∧ M.SuccessorOf j i ∧ ∃ u, M.mem u D ∧ ∃ v, M.mem v D ∧
      Rd_entry_d i u s ∧ Rd_entry_d j v s ∧ ∃ c, M.mem c J ∧ ∃ E, M.mem E P ∧
        KPair_d M p c E ∧ Eb_witness_d ω κ L B J K V R F G v u c E := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      KP.succ0_sat_l hZF.1, rd_entry0_sat_l hZF.1, kpair0_sat_l hZF.1, eb_witness_sat_l hZF.1]; rfl
  obtain ⟨H, hH, hf, select⟩ := sc_uniform_source_l hZF source.omega source.transitive model source.theory φ
    (.existsMem _ (.conj (KP.succ0_delta_l ..) (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (eb_witness_delta_l ..))))))))))
    ρ (Fin.cases hP (Fin.cases hs (Fin.cases hD (Fin.cases hG (Fin.cases hF (Fin.cases hR (Fin.cases hV
      (Fin.cases hJ (Fin.cases hB (Fin.cases hL (Fin.cases source.finite.mem_l (Fin.cases source.cardinal_mem (fun _ => source.omega_mem)))))))))))))
    source.omega_mem hT (fun i hi => by
      obtain ⟨j, hji, hj⟩ := source.omega.1.2 i hi
      obtain ⟨u, hu, hiu⟩ := fn.2.1 i hi
      obtain ⟨v, hv, hjv⟩ := fn.2.1 j hj
      obtain ⟨a, ha, f, hff, b, hb, g, hg, vp, up, c, hc, U, hU, hcU, E, hE, constraint⟩ := links i j u v hji hiu hjv
      obtain ⟨p, hp⟩ := (kp_pair_l (ZF.modelsKP hZF)).total c E
      have ep := (union E).mpr ⟨U, hU, hE⟩
      exact ⟨p, (product p).mpr ⟨c, hc, E, ep, hp⟩, (sat i p).mpr
        ⟨j, hj, hji, u, hu, v, hv, hiu, hjv, c, hc, E, ep, hp, a, ha, f, hff, b, hb, g, hg, vp, up, U, hU, hcU, hE, constraint⟩⟩)
  let η : Env M 3 := ⟨Fin.cases H (Fin.cases T (fun _ => P)), fun _ => P⟩
  let ψ : BinarySchema 3 := { body := Formula.existsMem (.bound 3) (Formula.existsMem (.bound 5)
    (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 4)) (kpair0_m (.bound 1) (.bound 2) .newest))) }
  have first i c : ψ.denote η i c ↔ ∃ p, M.mem p T ∧ ∃ E, M.mem E P ∧ Rd_entry_d i p H ∧ KPair_d M p c E := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, kpair0_sat_l hZF.1]; rfl
  obtain ⟨A, hA, fa, firsts⟩ := sc_uniform_source_l hZF source.omega source.transitive model source.theory ψ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (kpair0_delta_l ..)))) η
    (Fin.cases hH (Fin.cases hT (fun _ => hP))) source.omega_mem hJ (fun i hi => by
      obtain ⟨p, hp, hip⟩ := hf.2.1 i hi
      obtain ⟨c, hc, E, hE, pair⟩ := (product p).mp hp
      exact ⟨c, hc, (first i c).mpr ⟨p, hp, E, hE, hip, pair⟩⟩)
  let ε : Env M 3 := ⟨Fin.cases H (Fin.cases T (fun _ => J)), fun _ => J⟩
  let χ : BinarySchema 3 := { body := Formula.existsMem (.bound 3) (Formula.existsMem (.bound 5)
    (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 4)) (kpair0_m (.bound 1) .newest (.bound 2)))) }
  have second i E : χ.denote ε i E ↔ ∃ p, M.mem p T ∧ ∃ c, M.mem c J ∧ Rd_entry_d i p H ∧ KPair_d M p c E := by
    simp only [χ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, kpair0_sat_l hZF.1]; rfl
  obtain ⟨C, hC, fc, seconds⟩ := sc_uniform_source_l hZF source.omega source.transitive model source.theory χ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (kpair0_delta_l ..)))) ε
    (Fin.cases hH (Fin.cases hT (fun _ => hJ))) source.omega_mem hP (fun i hi => by
      obtain ⟨p, hp, hip⟩ := hf.2.1 i hi
      obtain ⟨c, hc, E, hE, pair⟩ := (product p).mp hp
      exact ⟨E, hE, (second i E).mpr ⟨p, hp, c, hc, hip, pair⟩⟩)
  have chosen i c E (hic : Rd_entry_d i c A) (hiE : Rd_entry_d i E C) :
      ∃ j u v, M.SuccessorOf j i ∧ Rd_entry_d i u s ∧ Rd_entry_d j v s ∧ Eb_witness_d ω κ L B J K V R F G v u c E := by
    obtain ⟨p, _, E', _, hip, hp⟩ := (first i c).mp (firsts i c hic)
    obtain ⟨p', _, c', _, hip', hp'⟩ := (second i E).mp (seconds i E hiE)
    have eq := (fn0_function_l (ZF.modelsKP hZF) hf).1.2 i p' p hip' hip
    subst p'
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
    obtain ⟨j, _, hji, u, _, v, _, hiu, hjv, c', _, E', _, hp', hw⟩ := (sat i p).mp (select i p hip)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp' hp
    exact ⟨j, u, v, hji, hiu, hjv, hw⟩
  refine ⟨P, A, C, hP, hA, hC, fa, fc, ?_, ?_⟩
  · intro i c E U hic hiE hcU
    obtain ⟨_, _, _, _, _, _, a, _, f, _, b, _, g, _, _, _, V', _, hcV, hE, _⟩ := chosen i c E hic hiE
    exact functional c V' U hcV hcU ▸ hE
  · intro i j u v c E hji hiu hjv hic hiE
    obtain ⟨j', u', v', hji', hiu', hjv', hw⟩ := chosen i c E hic hiE
    have ej := Structure.SuccessorOf.eq hZF.1 hji' hji
    subst j'
    have eu := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 i u' u hiu' hiu
    have ev := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 j v' v hjv' hjv
    exact ev ▸ eu ▸ hw

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共同纤维把下降代表列变成实际下降值列

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

/-! ## 超幂外部下降链的源内回收

统一值域界后，下降链可提升到源内的有界代表关系。该关系逐对读取原极限，
因此已有枝反射给出源中实际存在的下降代表图，供内部共同纤维条件使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_bounded_desc_l {ω κ K L X R₀ R F J O Z A p T S q C W g B R' : M.Domain}
    (hDC : Dc_d I ω) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R₀)
    (branches : Sc_branch_d ω X) (power : Sc_power_d X) (family : Em_source_d ω κ L X F)
    (hL : M.mem L X) (hF : M.mem F X) (hB : M.mem B X) (hR : M.mem R' X)
    (relation : ∀ x y, M.mem x B → M.mem y B → (Rd_entry_d x y R' ↔ Rd_entry_d x y R))
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (fn : Fn0_d ω C g) (desc : Wf_desc_d W g)
    (bounded : ∀ i E, Rd_entry_d i E g → ∃ n a D f, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧
      Ep_space_d κ n D ∧ M.mem f X ∧ Fn0_d D B f ∧ Ep_repr_d q a f E) : ∃ P G D V Q s,
      Eb_pool_d ω κ L X B J K P G D ∧ M.mem V X ∧ M.mem Q X ∧ M.IsRangeOf I V F ∧
      (∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L B J K V R' F G u v) ∧
      M.mem s X ∧ Fn0_d ω D s ∧ Wf_desc_d Q s := by
  obtain ⟨P, G, D, V, Q, e, pool, hV, hQ, range, _, _, _, edges, quotient, covers⟩ :=
    eb_graph_l hZF source power family system limit hL hF hB hR relation
  let ρ : Env M 3 := ⟨Fin.cases C (Fin.cases g (fun _ => e)), fun _ => C⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 2) (.conj (rd_entry0_m (.bound 2) .newest (.bound 4)) (rd_entry0_m (.bound 1) .newest (.bound 5))) }
  have sat i u : φ.denote ρ i u ↔ ∃ E, M.mem E C ∧ Rd_entry_d i E g ∧ Rd_entry_d u E e := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨f, hf, select⟩ := dc_uniformize_formula_l hZF φ ρ source.omega hDC (X := D) (fun i hi => by
    obtain ⟨E, he, hiE⟩ := fn.2.1 i hi
    obtain ⟨n, a, Y, f, hn, ha, hna, space, hfx, hfn, value⟩ := bounded i E hiE
    obtain ⟨u, hu, hue⟩ := covers n a Y f E hn ha hna space hfx hfn value
    exact ⟨u, hu, (sat i u).mpr ⟨E, he, hiE, hue⟩⟩)
  have decreasing : Wf_desc_d Q f := by
    intro i j u v hij hiu hjv
    obtain ⟨E, _, hiE, hue⟩ := (sat i u).mp (select i u hiu)
    obtain ⟨H, _, hjH, hvh⟩ := (sat j v).mp (select j v hjv)
    exact (quotient v u H E hvh hue).mpr (desc i j E H hij hiE hjH)
  obtain ⟨s, hs, sf, sd⟩ := branches D Q pool.carrier hQ ⟨f, hf, decreasing⟩
  exact ⟨P, G, D, V, Q, s, pool, hV, hQ, range, edges, hs, sf, sd⟩

theorem ep_source_desc_l {ω κ K L X R F J O Z A p T S q c C W g : M.Domain}
    (hDC : Dc_d I ω) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (branches : Sc_branch_d ω X) (cover : Sc_cover_d X) (power : Sc_power_d X)
    (family : Em_source_d ω κ L X F) (hL : M.mem L X) (hF : M.mem F X)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (model : Smdl_d I c C W) (elementary : Di_elementary_d I ω O A p T S)
    (fn : Fn0_d ω C g) (desc : Wf_desc_d W g) : ∃ B R' P G D V Q s,
      M.mem B X ∧ M.mem R' X ∧ (∀ x y, Rd_entry_d x y R' ↔ M.mem x B ∧ M.mem y B ∧ M.mem x y) ∧
      Eb_pool_d ω κ L X B J K P G D ∧ M.mem V X ∧ M.mem Q X ∧ M.IsRangeOf I V F ∧
      (∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L B J K V R' F G u v) ∧
      M.mem s X ∧ Fn0_d ω D s ∧ Wf_desc_d Q s := by
  obtain ⟨B, hB, _, bounded⟩ := ep_desc_bound_l hZF source cover family system limit model elementary fn desc
  obtain ⟨b, code⟩ := source.code
  let membership : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  obtain ⟨R', hR, _, rel⟩ := sc_relation_source_l hZF source.omega source.transitive code source.theory membership (.mem ..)
    ⟨Fin.elim0, fun _ => B⟩ (fun i => Fin.elim0 i) hB hB
  have read x y : Rd_entry_d x y R' ↔ M.mem x B ∧ M.mem y B ∧ M.mem x y :=
    (rel x y).trans (and_congr_right fun _ => and_congr_right fun _ => Formula.satisfies_mem_iff ..)
  have relation x y (hx : M.mem x B) (hy : M.mem y B) : Rd_entry_d x y R' ↔ Rd_entry_d x y R :=
    ⟨fun h => (code.2 x y).mpr ⟨source.transitive B hB x hx, source.transitive B hB y hy, ((read x y).mp h).2.2⟩,
      fun h => (read x y).mpr ⟨hx, hy, ((code.2 x y).mp h).2.2⟩⟩
  obtain ⟨P, G, D, V, Q, s, data⟩ := ep_bounded_desc_l hZF hDC source branches power family hL hF hB hR relation system limit fn desc bounded
  exact ⟨B, R', P, G, D, V, Q, s, hB, hR, read, data⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 所属模型内部短扩展器的实际施加良基性

外部下降链先在施加源中统一有界并回收为代表下降列；源内共同约束层再
送回所属模型。其内部共同纤维条件给出背景成员下降列，与基础公理矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一内部扩展器把源内代表下降图实现为原有界关系的下降图。 -/
theorem It_local_d.realize_desc_l {ω κ K X R K' Y R' L F V B R₀ J P₀ G D V₀ s : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y R')
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω Y) (hV : M.mem V Y) (owner_power : FilterZF.Source_d Y K' V)
    (loc : It_local_d I ω Y R' κ L F) (hB : M.mem B X) (hR₀ : M.mem R₀ X)
    (indices : ∀ a, M.mem a J ↔ Ei_d ω L a) (pool : Eb_pool_d ω κ L X B J K P₀ G D) (hV₀ : M.mem V₀ X)
    (hs : M.mem s X) (fs : Fn0_d ω D s)
    (links : ∀ i j u v, M.SuccessorOf j i → Rd_entry_d i u s → Rd_entry_d j v s → Eb_link_d ω κ L B J K V₀ R₀ F G v u) :
    ∃ v, Fn0_d ω B v ∧ Wf_desc_d R₀ v := by
  have family := loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hV owner_power)
  have local_copy := loc
  obtain ⟨_, _, hL, hF, _⟩ := local_copy
  obtain ⟨P, N, H, hP, hN, hH, fn, fh, large, constraints⟩ := eb_source_constraints_l hZF source (inside L hL) hB
    pool.indices pool.functions hV₀ hR₀ (inside F hF) pool.carrier hs fs family.function links
  obtain ⟨J', _, seq⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 L (inside L hL)
  have supports : Fn0_d ω J' N := fn.retarget_l (fun i a hia => by
    obtain ⟨n, hn, ha, _⟩ := (indices a).mp (fn.bound_l hia).2
    exact (seq a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩)
  obtain ⟨e, h, _, _, fe, fh', _, realize⟩ := es_source_joint_fiber_l hZF source owner inside agree owner_branches loc
    hV owner_power hP hN hH seq supports fh large
  exact eb_desc_realize_l hZF source.omega pool fs fn fh fe fh' realize constraints

theorem It_local_d.source_wf_l {ω κ K X R K' Y R' L F V J O Z A p T S q c C W : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y R')
    (hDC : Dc_d I ω) (branches : Sc_branch_d ω X) (cover : Sc_cover_d X) (power : Sc_power_d X)
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω Y) (hV : M.mem V Y) (owner_power : FilterZF.Source_d Y K' V)
    (loc : It_local_d I ω Y R' κ L F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (model : Smdl_d I c C W) (elementary : Di_elementary_d I ω O A p T S) : Wf_rel_d C W := by
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hV owner_power)).transfer_l reverse
  have local_copy := loc
  obtain ⟨_, _, hL, hF, _⟩ := local_copy
  apply wf_of_no_desc_l hZF hDC
  intro g fg dg
  obtain ⟨B, R₀, P₀, G, D, V₀, Q, s, hB, hR₀, membership, pool, hV₀, _, _, edges, hs, fs, ds⟩ :=
    ep_source_desc_l hZF hDC source branches cover power family (inside L hL) (inside F hF) system limit model elementary fg dg
  obtain ⟨v, fv, dv⟩ := loc.realize_desc_l hZF source owner inside agree owner_branches hV owner_power hB hR₀ system.indices pool hV₀ hs fs
    (fun i j u v hij hiu hjv => ((edges v u).mp (ds i j u v hij hiu hjv)).2.2)
  have wf : Wf_rel_d B R₀ := by
    intro A _ hn
    obtain ⟨a, ha, minimal⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) hn
    exact ⟨a, ha, fun b hb hba => minimal b hb ((membership b a).mp hba).2.2⟩
  exact wf_no_desc_l hZF source.omega wf fv dv

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 内部所属判断自动生成实际良基超幂与坍塌

该入口读取所属模型中的原短扩展器公式，构造施加源的全部实际分量、定向
极限及传递坍塌。每个良基性见证均来自源内共同约束，未要求背景短扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.limit_l {ω κ K X R K' Y S L F V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S)
    (branches : Sc_branch_d ω X) (cover : Sc_cover_d X) (power : Sc_power_d X)
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω Y) (hV : M.mem V Y) (owner_power : FilterZF.Source_d Y K' V)
    (loc : It_local_d I ω Y S κ L F) : Ep_limit_d hZF ω κ L X R F := by
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hV owner_power)).transfer_l reverse
  obtain ⟨J, O, Z, A, p, T, U, q, c, C, W, system, limit, model, elementary⟩ :=
    loc.apply_l hZFC source owner hV owner_power reverse
  have wf := loc.source_wf_l hZF source owner (ZFC.dc_l I hZFC source.omega) branches cover power
    inside agree owner_branches hV owner_power system limit model elementary
  exact ⟨J, O, Z, A, p, T, U, q, c, C, W, system, limit, model, wf, elementary,
    ep_collapse_l hZF source family system limit model elementary wf⟩

end YesMetaZFC.SetTheory.LargeCardinal
