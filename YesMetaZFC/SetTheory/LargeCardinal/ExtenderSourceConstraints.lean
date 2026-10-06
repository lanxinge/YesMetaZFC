import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedNodes
import YesMetaZFC.Model.SetTheory.Internal.SourceFamily

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
    (source : Ep_source_d hZF ω κ K X R₀) (hL : M.mem L X) (hB : M.mem B X)
    (hJ : M.mem J X) (hG : M.mem G X) (hV : M.mem V X) (hR : M.mem R X) (hF : M.mem F X)
    (hD : M.mem D X) (hs : M.mem s X) (fn : Fn0_d ω D s)
    (functional : ∀ a U V, Rd_entry_d a U F → Rd_entry_d a V F → U = V)
    (links : ∀ i j u v, M.SuccessorOf j i → Rd_entry_d i u s → Rd_entry_d j v s → Eb_link_d ω κ L B J K V R F G v u) :
    ∃ P A C, M.mem P X ∧ M.mem A X ∧ M.mem C X ∧ Fn0_d ω J A ∧ Fn0_d ω P C ∧
      (∀ i c E U, Rd_entry_d i c A → Rd_entry_d i E C → Rd_entry_d c U F → M.mem E U) ∧
      ∀ i j u v c E, M.SuccessorOf j i → Rd_entry_d i u s → Rd_entry_d j v s →
        Rd_entry_d i c A → Rd_entry_d i E C → Eb_witness_d ω κ L B J K V R F G v u c E := by
  obtain ⟨code, model⟩ := source.code
  obtain ⟨P, hP, union⟩ := source.theory.algebra.union V hV
  obtain ⟨T, hT, product⟩ := source.theory.algebra.product J P hJ hP
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
      (Fin.cases hJ (Fin.cases hB (Fin.cases hL (Fin.cases source.finite_mem (Fin.cases source.cardinal_mem (fun _ => source.omega_mem)))))))))))))
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
