import YesMetaZFC.Model.Forcing.Internal.Names.Sequence
import YesMetaZFC.Model.Forcing.Proper.Master.Basic
import YesMetaZFC.Model.Forcing.Internal.Forcing.Rules

/-! # 对内部公式标签及有限名称列统一构造判定集

标签为 (公式码,变量号)，两者用规范名称传入；参数列由唯一的函数图名称传入。
见证限定在给定的实际地集合 X 中，判定集始终是 B 的子集。正文是固定原公式，
可取内部满足关系的统一定义，而标签和参数长度均不限制为外部标准值。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Ng_rule_d {n} (φ : UnarySchema (n+3)) (ρ : Env M n) (B R z b l f p t : M.Domain) : Prop :=
  Name_d M B t ∧ ∃ a i c d s, KPair_d M l a i ∧ Check_d M b a c ∧ Check_d M b i d ∧
    Nseq_d M B b f s ∧ Forces_d M B R z φ.body ((((ρ.push c).push d).push s).push t) p

def ng_rule_m {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b l f p t : Term d) : Formula 1 d :=
  .conj (name_m B t) (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (kpair_m l.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3))
      (.conj (check_m b.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2))
      (.conj (check_m b.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
      (.conj (nseq_m B.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken
        f.weaken.weaken.weaken.weaken.weaken .newest)
        (force_at_m φ.body (Fin.cases t.weaken.weaken.weaken.weaken.weaken
          (Fin.cases .newest (Fin.cases (.bound 1) (Fin.cases (.bound 2)
            (fun i => (e i).weaken.weaken.weaken.weaken.weaken)))))
          B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken
          z.weaken.weaken.weaken.weaken.weaken p.weaken.weaken.weaken.weaken.weaken))))))))))

@[simp] theorem ng_rule_closed_l {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b l f p t : Term d) (he : ∀ i, (e i).freeSupport = [])
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hb : b.freeSupport = []) (hl : l.freeSupport = []) (hf : f.freeSupport = [])
    (hp : p.freeSupport = []) (ht : t.freeSupport = []) :
    (ng_rule_m φ e B R z b l f p t).FreeClosed := by
  have hargs : ∀ i, (Fin.cases t.weaken.weaken.weaken.weaken.weaken
      (Fin.cases .newest (Fin.cases (.bound 1) (Fin.cases (.bound 2)
        (fun i => (e i).weaken.weaken.weaken.weaken.weaken)))) i : Term (d+5)).freeSupport = [] :=
    Fin.cases (by simpa using ht) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => by simpa using he i))))
  simp -implicitDefEqProofs [ng_rule_m, Definitional.Formula.FreeClosed, φ.freeClosed, *]

theorem ng_rule_sat_l (hE : Extensional M) {n d} (φ : UnarySchema (n+3)) (ρ : Env M d)
    (e : Fin n → Term d) (B R z b l f p t : Term d) :
    Formula.satisfies ρ (ng_rule_m φ e B R z b l f p t) ↔
      Ng_rule_d φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (B.eval ρ) (R.eval ρ) (z.eval ρ)
        (b.eval ρ) (l.eval ρ) (f.eval ρ) (p.eval ρ) (t.eval ρ) := by
  simp only [ng_rule_m, Ng_rule_d, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    name_sat_l M hE, kpair_sat_l M hE, check_sat_l M hE, nseq_sat_l M hE,
    force_at_sat_l, args_cons_l, Definitional.Term.eval_weaken]
  rfl

theorem ng_rule_decode_l (hZF : M.Models ZF) {n} (φ : UnarySchema (n+3)) (ρ : Env M n)
    {B R z b l f p t a i c d s} (hl : KPair_d M l a i)
    (hc : Check_d M b a c) (hd : Check_d M b i d) (hs : Nseq_d M B b f s) :
    Ng_rule_d φ ρ B R z b l f p t ↔ Name_d M B t ∧
      Forces_d M B R z φ.body ((((ρ.push c).push d).push s).push t) p := by
  constructor
  · rintro ⟨ht, a', i', c', d', s', hl', hc', hd', hs', hp⟩
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hl' hl
    have hcc := check_unique_l M hZF.1 (check_ind_l M hZF) b a' c' c hc' hc
    have hdd := check_unique_l M hZF.1 (check_ind_l M hZF) b i' d' d hd' hd
    have hss := nseq_unique_l M hZF.1 hs' hs
    subst c' d' s'
    exact ⟨ht, hp⟩
  · exact fun ⟨ht, hp⟩ => ⟨ht, a, i, c, d, s, hl, hc, hd, hs, hp⟩

def Ng_rule_has_d {n} (φ : UnarySchema (n+3)) (ρ : Env M n) (B R z b X l f p : M.Domain) : Prop :=
  ∃ t, M.mem t X ∧ Ng_rule_d φ ρ B R z b l f p t

def ng_rule_has_m {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b X l f p : Term d) : Formula 1 d :=
  .existsE (.conj (.mem .newest X.weaken)
    (ng_rule_m φ (fun i => (e i).weaken) B.weaken R.weaken z.weaken b.weaken l.weaken f.weaken p.weaken .newest))

@[simp] theorem ng_rule_has_closed_l {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b X l f p : Term d) (he : ∀ i, (e i).freeSupport = [])
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hb : b.freeSupport = []) (hX : X.freeSupport = []) (hl : l.freeSupport = [])
    (hf : f.freeSupport = []) (hp : p.freeSupport = []) :
    (ng_rule_has_m φ e B R z b X l f p).FreeClosed := by
  simp -implicitDefEqProofs [ng_rule_has_m, Definitional.Formula.FreeClosed, *]

theorem ng_rule_has_sat_l (hE : Extensional M) {n d} (φ : UnarySchema (n+3)) (ρ : Env M d)
    (e : Fin n → Term d) (B R z b X l f p : Term d) :
    Formula.satisfies ρ (ng_rule_has_m φ e B R z b X l f p) ↔
      Ng_rule_has_d φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (B.eval ρ) (R.eval ρ) (z.eval ρ)
        (b.eval ρ) (X.eval ρ) (l.eval ρ) (f.eval ρ) (p.eval ρ) := by
  simp only [ng_rule_has_m, Ng_rule_has_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, ng_rule_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Ng_rule_decide_d {n} (φ : UnarySchema (n+3)) (ρ : Env M n) (B R z b X l f D : M.Domain) : Prop :=
  ∀ p, M.mem p D ↔ M.mem p B ∧ p ≠ z ∧ (Ng_rule_has_d φ ρ B R z b X l f p ∨
    Neg_d M B R z (Ng_rule_has_d φ ρ B R z b X l f) p)

def ng_rule_decide_m {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b X l f D : Term d) : Formula 1 d :=
  .forallE (.iff (.mem .newest D.weaken) (.conj (.mem .newest B.weaken)
    (.conj (.neg (Formula.extensionalEq .newest z.weaken)) (.disj
      (ng_rule_has_m φ (fun i => (e i).weaken) B.weaken R.weaken z.weaken b.weaken X.weaken l.weaken f.weaken .newest)
      (.forallE (.imp (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest (.bound 1))
        (.neg (ng_rule_has_m φ (fun i => (e i).weaken.weaken) B.weaken.weaken R.weaken.weaken
          z.weaken.weaken b.weaken.weaken X.weaken.weaken l.weaken.weaken f.weaken.weaken .newest))))))))

@[simp] theorem ng_rule_decide_closed_l {n d} (φ : UnarySchema (n+3)) (e : Fin n → Term d)
    (B R z b X l f D : Term d) (he : ∀ i, (e i).freeSupport = [])
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hb : b.freeSupport = []) (hX : X.freeSupport = []) (hl : l.freeSupport = [])
    (hf : f.freeSupport = []) (hD : D.freeSupport = []) :
    (ng_rule_decide_m φ e B R z b X l f D).FreeClosed := by
  simp -implicitDefEqProofs [ng_rule_decide_m, Definitional.Formula.FreeClosed, *]

theorem ng_rule_decide_sat_l (hE : Extensional M) {n d} (φ : UnarySchema (n+3)) (ρ : Env M d)
    (e : Fin n → Term d) (B R z b X l f D : Term d) :
    Formula.satisfies ρ (ng_rule_decide_m φ e B R z b X l f D) ↔
      Ng_rule_decide_d φ ⟨fun i => (e i).eval ρ, ρ.free⟩ (B.eval ρ) (R.eval ρ) (z.eval ρ)
        (b.eval ρ) (X.eval ρ) (l.eval ρ) (f.eval ρ) (D.eval ρ) := by
  simp only [ng_rule_decide_m, Ng_rule_decide_d, Neg_d, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_disj_iff,
    ng_rule_has_sat_l hE, Formula.satisfies_imp_iff, below_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

/-- 每个内部标签和每条参数图都有实际判定集，无需先假定小模型的闭包。 -/
theorem ng_rule_decide_exists_l (hZF : M.Models ZF) {n} (φ : UnarySchema (n+3))
    (ρ : Env M n) (B R z b X l f : M.Domain) : ∃ D, Ng_rule_decide_d φ ρ B R z b X l f D := by
  let η := (((((((ρ.push B).push R).push z).push b).push X).push l).push f)
  let ψ : UnarySchema (n+7) := {
    body := ng_rule_has_m φ (fun i => .bound ⟨i.val+8, by omega⟩)
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hψ p : ψ.denote η p ↔ Ng_rule_has_d φ ρ B R z b X l f p := by
    have h := ng_rule_has_sat_l hZF.1 φ (η.push p) (fun i => .bound ⟨i.val+8, by omega⟩)
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    exact h
  obtain ⟨k, χ, δ, hχ⟩ := defined_decide_l M hZF.1 ⟨n+7, ψ, η, hψ⟩ B R z
  let θ : UnarySchema (k+1) := {
    body := .conj (.neg (Formula.extensionalEq .newest (.bound 1)))
      (pred_m χ (fun i => .bound ⟨i.val+2, by omega⟩) .newest) }
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF θ (δ.push z) B
  refine ⟨D, fun p => (hD p).trans (and_congr_right fun _ => ?_)⟩
  simp only [θ, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, pred_sat_l M]
  exact and_congr Iff.rfl (hχ p)

theorem Ng_rule_decide_d.dense_l {n φ ρ B R z b X l f D}
    (O : Cond_order_d M B R z) (h : @Ng_rule_decide_d M n φ ρ B R z b X l f D) :
    Dense_set_d M B R z D := by
  classical
  refine ⟨fun p hp => ⟨((h p).mp hp).1, ((h p).mp hp).2.1⟩, fun p hp hz => ?_⟩
  by_cases he : ∃ q, Below_d M B R z q p ∧ Ng_rule_has_d φ ρ B R z b X l f q
  · obtain ⟨q, hq, hφ⟩ := he
    exact ⟨q, hq, (h q).mpr ⟨hq.1, hq.2.1, Or.inl hφ⟩⟩
  · exact ⟨p, below_refl_l O hp hz, (h p).mpr
      ⟨hp, hz, Or.inr (fun q hq hφ => he ⟨q, hq, hφ⟩)⟩⟩

end YesMetaZFC.Model.Forcing.Internal
