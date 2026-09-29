import YesMetaZFC.Model.Forcing.InternalNameConstruction

/-! # 内部名称扩张的全收集模式

在“源子名称 × 条件集”上，内部收集为每个能够力迫见证的条件选取一个名称。
无见证的输入用空名称处理；随后分离有效名称并统一加上一个被接受的标签。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v

theorem args_cons_l {M : SetTheory.Structure.{u}} {n m} (ρ : Env M m) (t : Term m) (e : Fin n → Term m) :
    (⟨fun i : Fin (n + 1) => (Fin.cases t e i : Term m).eval ρ, ρ.free⟩ : Env M (n + 1)) =
      (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M n).push (t.eval ρ) := by
  rw [Env.mk.injEq]
  constructor
  · funext i; exact Fin.cases rfl (fun _ => rfl) i
  · rfl

def witness_m {n m} (φ : BinarySchema n) (e : Fin n → Term m) (B R z a p t : Term m) : Formula 1 m :=
  .conj (name_m B t) (.forallE (.imp
    (.conj (name_m B.weaken .newest) (force_at_m φ.body
      (Fin.cases .newest (Fin.cases a.weaken (fun i => (e i).weaken)))
      B.weaken R.weaken z.weaken p.weaken))
    (force_at_m φ.body (Fin.cases t.weaken (Fin.cases a.weaken (fun i => (e i).weaken)))
      B.weaken R.weaken z.weaken p.weaken)))

@[simp] theorem witness_closed_l {n m} (φ : BinarySchema n) (e : Fin n → Term m) (B R z a p t : Term m)
    (he : ∀ i, (e i).freeSupport = []) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (ha : a.freeSupport = []) (hp : p.freeSupport = []) (ht : t.freeSupport = []) :
    (witness_m φ e B R z a p t).FreeClosed := by
  have hc {k} (s : Term (m+1)) (f : Fin k → Term (m+1)) (hs : s.freeSupport = [])
      (hf : ∀ i, (f i).freeSupport = []) : ∀ i : Fin (k+1),
      (Fin.cases s f i : Term (m+1)).freeSupport = [] := by
    intro i
    exact Fin.cases hs hf i
  have hn := hc .newest (Fin.cases a.weaken (fun i => (e i).weaken)) rfl
    (hc a.weaken (fun i => (e i).weaken) (by simpa using ha) (fun i => by simpa using he i))
  have hv := hc t.weaken (Fin.cases a.weaken (fun i => (e i).weaken)) (by simpa using ht)
    (hc a.weaken (fun i => (e i).weaken) (by simpa using ha) (fun i => by simpa using he i))
  simp -implicitDefEqProofs [witness_m, Definitional.Formula.FreeClosed, *]

theorem witness_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n m}
    (φ : BinarySchema n) (ρ : Env M m) (e : Fin n → Term m) (B R z a p t : Term m) :
    Formula.satisfies ρ (witness_m φ e B R z a p t) ↔
      Name_d M (B.eval ρ) (t.eval ρ) ∧ ∀ v, Name_d M (B.eval ρ) v →
        Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ.body
          ((⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M n).push (a.eval ρ) |>.push v) (p.eval ρ) →
        Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ.body
          ((⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M n).push (a.eval ρ) |>.push (t.eval ρ)) (p.eval ρ) := by
  simp only [witness_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, name_sat_l M hE, force_at_sat_l, args_cons_l,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact and_congr_right fun _ => forall_congr' fun _ =>
    ⟨fun h hn hv => h ⟨hn, hv⟩, fun h ⟨hn, hv⟩ => h hn hv⟩

variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
  (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M) (hN : ∃ t, Name_d M B t)
local notation "E" => ext_structure_l (name_domain_l M hM hL B hN) U
include O hZF hU

theorem internal_collection_l {n} (φ : BinarySchema n) (η : Env E n) (A : (E).Domain)
    (h : ∀ x : (E).Domain, x.1 ∈ A.1 → ∃ y : (E).Domain,
      Formula.satisfies ((η.push x).push y) φ.body) :
    ∃ C : (E).Domain, ∀ x : (E).Domain, x.1 ∈ A.1 → ∃ y : (E).Domain,
      y.1 ∈ C.1 ∧ Formula.satisfies ((η.push x).push y) φ.body := by
  classical
  obtain ⟨ρ, hρ⟩ := lift_env_l hM hL hN η
  obtain ⟨t, ht, hA⟩ := value_name_l hM hL hN A
  obtain ⟨S, htS, hS⟩ := ht
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨K, hK⟩ := ZF.exists_cartesianProduct hZF I S B
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hen := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he
  let δ := ((ρ.push B).push R).push z
  let es : Fin n → Term (n + 7) := fun i => .bound ⟨i.val + 7, by omega⟩
  let ψ : BinarySchema (n + 3) := {
    body := .existsE (.existsE (.conj (kpair_m (.bound 3) (.bound 1) .newest)
      (witness_m φ es (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest (.bound 2))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, es] }
  have hψ k v : ψ.denote δ k v ↔ ∃ a p, KPair_d M k a p ∧ Name_d M B v ∧
      ∀ w, Name_d M B w → Forces_d M B R z φ.body ((ρ.push a).push w) p →
        Forces_d M B R z φ.body ((ρ.push a).push v) p := by
    have hs a p : (⟨fun i => (es i).eval ((((δ.push k).push v).push a).push p),
        ((((δ.push k).push v).push a).push p).free⟩ : Env M n) = ρ := by cases ρ; rfl
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, witness_sat_l hZF.1, hs]
    rfl
  obtain ⟨T, hT⟩ := ZF.collection_exists_d hZF ψ δ K (fun k hk => by
    obtain ⟨a, _, p, _, hk⟩ := (hK k).mp hk
    by_cases h : ∃ v, Name_d M B v ∧ Forces_d M B R z φ.body ((ρ.push a).push v) p
    · obtain ⟨v, hv, hφ⟩ := h
      exact ⟨v, (hψ k v).mpr ⟨a, p, hk, hv, fun _ _ _ => hφ⟩⟩
    · exact ⟨e, (hψ k e).mpr ⟨a, p, hk, hen, fun v hv hφ => False.elim (h ⟨v, hv, hφ⟩)⟩⟩)
  let ρB : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  let ν : UnarySchema 1 := { body := name_m (.bound 1) (.bound 0) }
  obtain ⟨F, hF⟩ := ZF.separation_exists_d hZF ν ρB T
  have hf v : M.mem v F ↔ M.mem v T ∧ Name_d M B v :=
    (hF v).trans (and_congr_right fun _ => name_sat_l M hZF.1 (ρB.push v) (.bound 1) (.bound 0))
  obtain ⟨b, hb⟩ := hU.inhabited
  let ρb : Env M 1 := ⟨fun _ => b, fun _ => b⟩
  obtain ⟨q, hq, _, hqE⟩ := name_comp_l M hZF BinarySchema.constantValue ρb B F
    (fun v hv => ((hf v).mp hv).2)
  obtain ⟨C, hC⟩ := name_value_l hM hL hN hq
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨a, c, ha, hc, hax⟩ := (val_mem_l M hA).mp hx
  obtain ⟨y, hxy⟩ := h x hx
  obtain ⟨v, hv, hvy⟩ := value_name_l hM hL hN y
  have hρ' := env_val_push_l hM hL hN (env_val_push_l hM hL hN hρ hax) hvy
  have hEval := formula_eval_l O hZF hU hM hL hN φ.body φ.freeClosed ((ρ.push a).push v)
    ((η.push x).push y) hρ'
  obtain ⟨p, hp, hpφ⟩ := hEval.2.mpr hxy
  obtain ⟨r, hr, _, hrp⟩ := hU.directed c p hc hp
  have hr' := hU.proper r hr
  have hrφ := hEval.1.1 p r (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ hpφ
  obtain ⟨k, hk⟩ := I.total a r
  obtain ⟨w, hwT, hw⟩ := hT k ((hK k).mpr ⟨a, (supp_entry_l M hS htS ha).1, r, hr'.1, hk⟩)
  obtain ⟨a', r', hk', hwN, hwφ⟩ := (hψ k w).mp hw
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hk hk'
  obtain ⟨y', hwy⟩ := name_value_l hM hL hN hwN
  refine ⟨y', (val_mem_l M hC).mpr ⟨w, b, (hqE w b).mpr ⟨(hf w).mpr ⟨hwT, hwN⟩,
    (hU.proper b hb).1, (Formula.denote_constantValue_iff hZF.1 ρb w b).mpr rfl⟩, hb, hwy⟩, ?_⟩
  exact (forcing_truth_l O hZF hU hM hL hN φ.body φ.freeClosed ((ρ.push a).push w)
    ((η.push x).push y') (env_val_push_l hM hL hN (env_val_push_l hM hL hN hρ hax) hwy)).mp
      ⟨r, hr, hwφ v hv hrφ⟩

end YesMetaZFC.Model.Forcing.Internal
