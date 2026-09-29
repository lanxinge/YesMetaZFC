import YesMetaZFC.Model.Forcing.InternalDefinability
import YesMetaZFC.SetTheory.DependentChoice

/-! # 模型内部可数闭性与可数稠密交

闭性只接收模型内部的函数图。稠密交的下降链由内部依赖选择构造，
因此不把外部 ω 链误认为模型能够收集的序列。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention}

def binary_pred_m {k n} (φ : BinarySchema k) (e : Fin k → Term n) (a b : Term n) : Formula 1 n :=
  pred_m ({ body := φ.body, freeClosed := φ.freeClosed } : UnarySchema (k + 1)) (Fin.cases a e) b

@[simp] theorem binary_pred_closed_l {k n} (φ : BinarySchema k) (e : Fin k → Term n) (a b : Term n)
    (he : ∀ i, (e i).freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) :
    (binary_pred_m φ e a b).FreeClosed := pred_m_freeClosed _ _ _ (Fin.cases ha he) hb

theorem binary_pred_sat_l {k n} (φ : BinarySchema k) (ρ : Env M n) (e : Fin k → Term n) (a b : Term n) :
    Formula.satisfies ρ (binary_pred_m φ e a b) ↔
      φ.denote (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k) (a.eval ρ) (b.eval ρ) := by
  rw [binary_pred_m, pred_sat_l]
  have he : (⟨fun i => (Fin.cases a e i : Term n).eval ρ, ρ.free⟩ : Env M (k+1)) =
      (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k).push (a.eval ρ) := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩
  rw [he]
  rfl

def Chain_d (I : 𝒞.Interpretation M) (B R z ω f : M.Domain) : Prop :=
  M.IsSetFunctionFromTo I f ω B ∧ (∀ i p, M.PairMember I i p f → p ≠ z) ∧
    ∀ i j p q, M.SuccessorOf j i → M.PairMember I i p f → M.PairMember I j q f → M.PairMember I q p R

def Closed_d (I : 𝒞.Interpretation M) (B R z ω : M.Domain) : Prop :=
  ∀ f, Chain_d I B R z ω f → ∃ q, M.mem q B ∧ q ≠ z ∧
    ∀ i p, M.PairMember I i p f → M.PairMember I q p R

variable {B R z ω : M.Domain} (O : Cond_order_d M B R z) (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
include O hZF

/-- 后继处递降的内部 ω 序列，在任意较晚指标处都更强。 -/
theorem chain_lower_l (hω : M.IsOmega ω) {f} (hf : Chain_d I B R z ω f) :
    ∀ i j p q, M.mem i j → Entry_d M i p f → Entry_d M j q f → Entry_d M q p R := by
  have h : ∀ j, M.mem j ω → ∀ i p q, M.mem i j → Entry_d M i p f → Entry_d M j q f → Entry_d M q p R := by
    apply hω.induction (fun j => ∀ i p q, M.mem i j → Entry_d M i p f → Entry_d M j q f → Entry_d M q p R)
    · let φ : UnarySchema 2 := {
        body := .forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound 3))
          (.imp (entry_m (.bound 2) (.bound 1) (.bound 5))
            (.imp (entry_m (.bound 3) .newest (.bound 5)) (entry_m .newest (.bound 1) (.bound 4))))))) }
      let ρ : Env M 2 := (⟨fun _ => f, fun _ => f⟩ : Env M 1).push R
      obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ ρ ω
      refine ⟨T, fun j => ?_⟩
      rw [hT j]
      simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_mem_iff, entry_sat_l M hZF.1]
      rfl
    · exact fun e he i _ _ hi _ _ => False.elim (he i hi)
    · intro k hk ih j hj i p q hij hip hjq
      obtain ⟨r, _, hkr⟩ := hf.1.2.2 k hk
      have hqr := hf.2.2 k j r q hj hkr hjq
      rcases (hj i).mp hij with hik | he
      · exact O.trans q r p (hf.1.output_mem_of_pairMember hjq)
          (hf.1.output_mem_of_pairMember hkr) (hf.1.output_mem_of_pairMember hip) hqr (ih i p r hik hip hkr)
      · have he := hZF.1.eq_of_same_members i k he
        subst k
        have he := hf.1.1.2 i p r hip hkr
        exact he.symm ▸ hqr
  exact fun i j p q hij hip hjq => h j (hf.1.input_mem_of_pairMember hjq) i p q hij hip hjq

omit hZF in
/-- 可数闭偏序中，模型内任意可数可定义稠密开族具有稠密交。 -/
theorem closed_intersection_l (hZFC : M.Models ZFC) (hω : M.IsOmega ω)
    (hc : Closed_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B R z ω)
    {n} (φ : BinarySchema n) (ρ : Env M n)
    (hd : ∀ i, M.mem i ω → ∀ p, M.mem p B → p ≠ z → Dense_d M B R z (φ.denote ρ i) p)
    (hl : ∀ i, M.mem i ω → Lower_d M B R z (φ.denote ρ i))
    {p} (hp : M.mem p B) (hn : p ≠ z) :
    ∃ q, Below_d M B R z q p ∧ ∀ i, M.mem i ω → φ.denote ρ i q := by
  let hZF := ZFC.models_zf_l hZFC
  let J := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let δ := ((((ρ.push ω).push B).push R).push z).push p
  let es : Fin n → Term (n+8) := fun i => .bound ⟨i.val+8, by omega⟩
  let ψ : UnarySchema (n+5) := {
    body := .existsE (.existsE (.conj (kpair_m (.bound 2) (.bound 1) .newest)
      (.conj (.mem (.bound 1) (.bound 7)) (.conj
        (below_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 3))
        (binary_pred_m φ es (.bound 1) .newest)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, es] }
  have hψ s : ψ.denote δ s ↔ ∃ i q, KPair_d M s i q ∧ M.mem i ω ∧ Below_d M B R z q p ∧ φ.denote ρ i q := by
    have he i q : (⟨fun j => (es j).eval (((δ.push s).push i).push q),
        (((δ.push s).push i).push q).free⟩ : Env M n) = ρ := by cases ρ; rfl
    simp only [UnarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, Formula.satisfies_mem_iff, below_sat_l M hZF.1, binary_pred_sat_l, he]
    rfl
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF J ω B
  obtain ⟨K, hK⟩ := ZF.separation_exists_d hZF ψ δ P
  have hk s : M.mem s K ↔ ∃ i q, KPair_d M s i q ∧ M.mem i ω ∧ Below_d M B R z q p ∧ φ.denote ρ i q := by
    rw [hK s]
    change (M.mem s P ∧ ψ.denote δ s) ↔ _
    rw [hψ]
    exact ⟨And.right, fun ⟨i, q, hs, hi, hq, hφ⟩ =>
      ⟨(hP s).mpr ⟨i, hi, q, hq.1, hs⟩, i, q, hs, hi, hq, hφ⟩⟩
  let η : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z
  let θ : BinarySchema 3 := {
    body := .existsE (.existsE (.existsE (.existsE (.conj (kpair_m (.bound 5) (.bound 3) (.bound 2))
      (.conj (kpair_m (.bound 4) (.bound 1) .newest) (.conj (Formula.isSuccessor (.bound 1) (.bound 3))
        (below_m (.bound 8) (.bound 7) (.bound 6) .newest (.bound 2)))))))) }
  have hθ s t : θ.denote η s t ↔ ∃ i q j r, KPair_d M s i q ∧ KPair_d M t j r ∧
      M.SuccessorOf j i ∧ Below_d M B R z r q := by
    simp only [BinarySchema.denote, θ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, Formula.satisfies_isSuccessor_iff, below_sat_l M hZF.1]
    rfl
  obtain ⟨T, _, hT⟩ := ZF.exists_setRelationOn_of_denote hZF J θ η K
  have ht : ∀ s, M.mem s K → ∃ t, M.mem t K ∧ Entry_d M s t T := by
    intro s hsK
    obtain ⟨i, q, hs, hi, hq, _⟩ := (hk s).mp hsK
    obtain ⟨j, hji, hj⟩ := hω.1.2 i hi
    obtain ⟨r, hr, hφ⟩ := hd j hj q hq.1 hq.2.1 q (below_refl_l O hq.1 hq.2.1)
    obtain ⟨t, htc⟩ := J.total j r
    have htK := (hk t).mpr ⟨j, r, htc, hj, below_trans_l O hp hr hq, hφ⟩
    exact ⟨t, htK, (hT s t).mpr ⟨hsK, htK, (hθ s t).mpr ⟨i, q, j, r, hs, htc, hji, hr⟩⟩⟩
  obtain ⟨e, he, heω⟩ := hω.1.1
  obtain ⟨q₀, hq₀, hφ₀⟩ := hd e heω p hp hn p (below_refl_l O hp hn)
  obtain ⟨s₀, hs₀⟩ := J.total e q₀
  obtain ⟨g, hg, hg₀, hgs⟩ := ZFC.dependent_choice_l J hZFC hω ((hk s₀).mpr ⟨e, q₀, hs₀, heω, hq₀, hφ₀⟩) ht
  have step i j s t (hji : M.SuccessorOf j i) (his : Entry_d M i s g) (hjt : Entry_d M j t g) :=
    (hθ s t).mp ((hT s t).mp (hgs i j s t hji his hjt)).2.2
  have index : ∀ i, M.mem i ω → ∀ s, Entry_d M i s g → ∃ q, KPair_d M s i q := by
    apply hω.induction (fun i => ∀ s, Entry_d M i s g → ∃ q, KPair_d M s i q)
    · let ξ : UnarySchema 1 := { body := .forallE (.imp (entry_m (.bound 1) .newest (.bound 2))
          (.existsE (kpair_m (.bound 1) (.bound 2) .newest))) }
      obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF ξ (⟨fun _ => g, fun _ => g⟩ : Env M 1) ω
      refine ⟨A, fun i => ?_⟩
      rw [hA i]
      simp only [ξ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_exists_iff, entry_sat_l M hZF.1, kpair_sat_l M hZF.1]
      rfl
    · intro a ha s hs
      have heq := hZF.1.eq_of_same_members a e (fun x => iff_of_false (ha x) (he x))
      subst a
      have heq := hg.1.2 e s s₀ hs (hg₀ e he)
      exact ⟨q₀, heq.symm ▸ hs₀⟩
    · intro i hi ih j hji t hjt
      obtain ⟨s, _, his⟩ := hg.2.2 i hi
      obtain ⟨q, hs⟩ := ih s his
      obtain ⟨a, b, c, d, hab, hcd, hca, _⟩ := step i j s t hji his hjt
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hab hs
      have heq := Structure.SuccessorOf.eq hZF.1 hca hji
      exact ⟨d, heq ▸ hcd⟩
  let χ : BinarySchema 1 := {
    body := .existsE (.conj (entry_m (.bound 2) .newest (.bound 3))
      (kpair_m .newest (.bound 2) (.bound 1))) }
  let γ : Env M 1 := ⟨fun _ => g, fun _ => g⟩
  have hχ i q : χ.denote γ i q ↔ ∃ s, Entry_d M i s g ∧ KPair_d M s i q := by
    simp only [BinarySchema.denote, χ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      entry_sat_l M hZF.1, kpair_sat_l M hZF.1]
    rfl
  have info {i s q} (his : Entry_d M i s g) (hs : KPair_d M s i q) :
      Below_d M B R z q p ∧ φ.denote ρ i q := by
    obtain ⟨a, b, hab, _, hbp, hφ⟩ := (hk s).mp (hg.output_mem_of_pairMember his)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hab hs
    exact ⟨hbp, hφ⟩
  obtain ⟨f, hf, hfe⟩ := ZF.exists_setFunctionFromTo_of_denote hZF J χ γ (source := ω) (target := B) (by
    intro i hi
    obtain ⟨s, _, his⟩ := hg.2.2 i hi
    obtain ⟨q, hs⟩ := index i hi s his
    exact ⟨q, (hχ i q).mpr ⟨s, his, hs⟩⟩) (by
    intro i _ q r hq hr
    obtain ⟨s, his, hsq⟩ := (hχ i q).mp hq
    obtain ⟨t, hit, htr⟩ := (hχ i r).mp hr
    have heq := hg.1.2 i s t his hit
    subst t
    exact (kpair_injective_l M hsq htr).2) (by
    intro i q _ hq
    obtain ⟨s, his, hsq⟩ := (hχ i q).mp hq
    exact (info his hsq).1.1)
  have pair {i q} (hi : Entry_d M i q f) := (hχ i q).mp ((hfe i q).mp hi).2
  have hchain : Chain_d J B R z ω f := by
    refine ⟨hf, fun i q hi => ?_, fun i j q r hji hi hj => ?_⟩
    · obtain ⟨s, his, hs⟩ := pair hi
      exact (info his hs).1.2.1
    · obtain ⟨s, his, hs⟩ := pair hi
      obtain ⟨t, hjt, ht⟩ := pair hj
      obtain ⟨a, b, c, d, hab, hcd, _, hdb⟩ := step i j s t hji his hjt
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hab hs
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hcd ht
      exact hdb.2.2
  obtain ⟨r, hr, hrz, hrs⟩ := hc f hchain
  obtain ⟨q, hq, heq⟩ := hf.2.2 e heω
  obtain ⟨s, hes, hs⟩ := pair heq
  refine ⟨r, ⟨hr, hrz, O.trans r q p hr hq hp (hrs e q heq) (info hes hs).1.2.2⟩, fun i hi => ?_⟩
  obtain ⟨q, hq, hiq⟩ := hf.2.2 i hi
  obtain ⟨s, his, hs⟩ := pair hiq
  exact hl i hi q r hq ⟨hr, hrz, hrs i q hiq⟩ (info his hs).2

end YesMetaZFC.Model.Forcing.Internal
