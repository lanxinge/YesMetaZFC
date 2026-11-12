import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyHistory
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

/-! # 实际共同层在当前原模型中的有限高度界

端点只来自历史中两行的真实共同层；模型关系由原树的同一代码列确定。
最大共同高度的唯一性使端点集成为有限行集的部分函数像。非空时取其
原生最大元，空集时取原模型的空序数，不加入跨行支撑码的任意组合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ic_height_d (I : kpair_convention_l.Interpretation M) (H Q N R σ n i l : M.Domain) : Prop :=
  Rr_truth_d I N R (KP.ord0_m .newest) (fun _ : Fin 1 => l) ∧
    ∃ X A π z Z α B u U β c d S L φ V W D t,
      Ic_at_d H i X A π z Z α ∧ Ic_at_d H n N B σ u U β ∧
      Rd_entry_d i c Q ∧ Rd_entry_d n d Q ∧ Smdl_d I c X S ∧ Smdl_d I d N R ∧
      Ic_agree_d I X S A π N R B σ L l φ V W D t

/-- 实际有限端点的最大元，空集时使用原模型的空序数。 -/
structure Ic_bound_d (I : kpair_convention_l.Interpretation M) (H Q N R σ n b : M.Domain) : Prop where
  ordinal : Rr_truth_d I N R (KP.ord0_m .newest) (fun _ : Fin 1 => b)
  origin : (∀ x, M.mem x N → ¬ Rd_entry_d x b R) ∨
    ∃ i, M.mem i n ∧ Ic_height_d I H Q N R σ n i b
  upper : ∀ i l, M.mem i n → Ic_height_d I H Q N R σ n i l → Rd_entry_d l b R ∨ l = b

def ic_height_m {d} (H Q N R σ n i l : Term d) : Formula 1 d :=
  .conj (rr_ord_m N R l) (set[d] ⟪∃ X A π z Z α B u U β c d S L φ V W D t,
    ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, ⌜i⌝ₛ, X, A, π, z, Z, α) ∧
    ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, ⌜n⌝ₛ, ⌜N⌝ₛ, B, ⌜σ⌝ₛ, u, U, β) ∧
    ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, c, ⌜Q⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, d, ⌜Q⌝ₛ) ∧
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, S) ∧
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(d, ⌜N⌝ₛ, ⌜R⌝ₛ) ∧
    ⌜ic_agree_m⌝ₚ(X, S, A, π, ⌜N⌝ₛ, ⌜R⌝ₛ, B, ⌜σ⌝ₛ, L, ⌜l⌝ₛ, φ, V, W, D, t)⟫)
derive_free_closed ic_height_m

theorem ic_height_sat_l (hKP : M.Models KP) {d} (η : Env M d) (H Q N R σ n i l : Term d) :
    Formula.satisfies η (ic_height_m H Q N R σ n i l) ↔
      Ic_height_d (kp_pair_l hKP) (H.eval η) (Q.eval η) (N.eval η) (R.eval η)
        (σ.eval η) (n.eval η) (i.eval η) (l.eval η) := by
  simp only [ic_height_m, Ic_height_d, Formula.satisfies_conj_iff, rr_ord_sat_l (kp_pair_l hKP),
    Formula.satisfies_exists_iff, ic_at_sat_l hKP.1, rd_entry0_sat_l hKP.1,
    smdl_sat_l (kp_pair_l hKP), ic_agree_sat_l hKP, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 每个旧行到当前行的共同端点唯一，不依赖共同层的见证选择。 -/
theorem Ic_history_d.height_unique_l {ω T Q G E L m H S Q' G' n N R σ i l l' : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L m H S Q' G')
    (hω : M.IsOmega ω) (qf : M.IsSetFunction I Q)
    (a : Ic_height_d I H Q N R σ n i l) (b : Ic_height_d I H Q N R σ n i l') : l = l' := by
  obtain ⟨_, X, A, π, z, Z, α, B, u, U, β, c, d, Rx, ρ, φ, V, W, D, t,
    ai, an, qi, _, mx, _, h⟩ := a
  obtain ⟨_, X', A', π', z', Z', α', B', u', U', β', c', d', Rx', ρ', φ', V', W', D', t',
    bi, bn, qi', _, mx', _, g⟩ := b
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := ai.unique_l (ZF.modelsKP hZF) hist.function bi
  have eq := (an.unique_l (ZF.modelsKP hZF) hist.function bn).2.1
  subst B'
  have eq := qf.2 i c' c qi' qi
  subst c'
  have eq := (smdl_unique_l I mx' mx).2
  subst Rx'
  obtain ⟨c₀, qc₀, _, row⟩ := hist.row_l hZF bi
  have eq := qf.2 i c₀ c qc₀ qi
  subst c₀
  obtain ⟨R₀, RA, _, a₀, _, _, mx₀, ma, _, _, _, _, _, _, map⟩ := row
  have eq := (smdl_unique_l I mx₀ mx).2
  subst R₀
  obtain ⟨_, _, _, own⟩ := hist.row_l hZF an
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, smap⟩ := own
  exact (h.height_unique_l hZF g hω mx ma map smap.1).2.1

/-- 端点集是内部有限行集的部分函数像。 -/
theorem Ic_history_d.height_set_l {ω T Q G E L m H S Q' G' n N R σ : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L m H S Q' G')
    (hω : M.IsOmega ω) (hn : M.mem n ω) (qf : M.IsSetFunction I Q) :
    ∃ D, Finite_d I ω D ∧ ∀ l, M.mem l D ↔
      ∃ i, M.mem i n ∧ Ic_height_d I H Q N R σ n i l := by
  let η : Env M 6 := ⟨Fin.cases n (Fin.cases σ (Fin.cases R
    (Fin.cases N (Fin.cases Q (fun _ => H))))), fun _ => N⟩
  let φ : BinarySchema 6 := {
    body := ic_height_m (.bound 7) (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat i l : φ.denote η i l ↔ Ic_height_d I H Q N R σ n i l := by
    simp only [φ, BinarySchema.denote, ic_height_sat_l (ZF.modelsKP hZF)]; rfl
  let ψ : UnarySchema 6 := { body := .existsE φ.body }
  obtain ⟨A, ha⟩ := ZF.separation_exists_d hZF ψ η n
  have domain i : M.mem i A ↔ M.mem i n ∧ ∃ l, φ.denote η i l :=
    (ha i).trans (and_congr_right fun _ => Formula.satisfies_exists_iff (η.push i) φ.body)
  have total i (hi : M.mem i A) := ((domain i).mp hi).2
  have single i (_ : M.mem i A) l l' (hl : φ.denote η i l) (hl' : φ.denote η i l') : l = l' :=
    hist.height_unique_l hZF hω qf ((sat i l).mp hl) ((sat i l').mp hl')
  obtain ⟨D, hd⟩ := ZF.exists_functionalImageOn hZF φ η A total single
  have fin : Finite_d I ω n := ⟨n, hn, ZF.exists_inclusionInjection hZF I (fun _ h => h)⟩
  refine ⟨D, ZF.finite_defined_image_l I hZF hω
    (ZF.finite_subset_l I hZF fin (fun i hi => ((domain i).mp hi).1)) φ η total single hd, ?_⟩
  intro l
  exact (hd l).trans ⟨fun ⟨i, hi, hl⟩ => ⟨i, ((domain i).mp hi).1, (sat i l).mp hl⟩,
    fun ⟨i, hi, hl⟩ => ⟨i, (domain i).mpr ⟨hi, l, (sat i l).mpr hl⟩, (sat i l).mpr hl⟩⟩

/-- 由实际端点集构造选择下一支撑所需的单一原生界。 -/
theorem Ic_history_d.height_bound_l {ω T Q G E L m H S Q' G' n N R B σ u U β c : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L m H S Q' G')
    (top : Ic_at_d H n N B σ u U β) (hω : M.IsOmega ω) (hn : M.mem n ω)
    (qf : M.IsSetFunction I Q) (qc : Rd_entry_d n c Q) (mn : Smdl_d I c N R) :
    ∃ b, Ic_bound_d I H Q N R σ n b := by
  classical
  obtain ⟨c₀, qc₀, _, row⟩ := hist.row_l hZF top
  have eq := qf.2 n c₀ c qc₀ qc
  subst c₀
  obtain ⟨R₀, RB, _, cb, _, _, mn₀, mb, _, small, _, _, _, _, map⟩ := row
  have eq := (smdl_unique_l I mn₀ mn).2
  subst R₀
  obtain ⟨D, finite, height⟩ := hist.height_set_l hZF hω hn qf (N := N) (R := R) (σ := σ)
  by_cases ne : ∃ l, M.mem l D
  · obtain ⟨b, hb, max⟩ := rr_finite_max_l hZF hω mn mb small.transitive map finite
      (fun l hl => by obtain ⟨_, _, h⟩ := (height l).mp hl; exact h.1) ne
    obtain ⟨i, hi, raw⟩ := (height b).mp hb
    exact ⟨b, raw.1, Or.inr ⟨i, hi, raw⟩,
      fun i l hi hl => max l ((height l).mpr ⟨i, hi, hl⟩)⟩
  · -- 空历史的界仍来自实际复制行：回拉工作源中的空集存在句子。
    let N₀ := smdl_structure_l I (R := R) mn.2.1
    obtain ⟨e, he, heω⟩ := hω.1.1
    have heB := small.transitive ω small.omega_mem e heω
    obtain ⟨a, ha⟩ := mn.2.1
    let φ : Formula 1 0 := .existsE (.forallE (.neg (.mem .newest (.bound 1))))
    let η : Env N₀ 0 := ⟨Fin.elim0, fun _ => ⟨a, ha⟩⟩
    let θ : Env (smdl_structure_l I (R := RB) mb.1.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨e, heB⟩⟩
    have valid : Formula.satisfies θ φ := ⟨⟨e, heB⟩, fun x hx => he x.val ((mb.2 x.val e).mp hx).2.2⟩
    obtain ⟨o, ho⟩ := (smap_source_l I hZF hω mn mb.1 map φ
      (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) η θ (fun i => Fin.elim0 i)).mpr valid
    have ord : Formula.satisfies (⟨fun _ => o, fun _ => o⟩ : Env N₀ 1) (KP.ord0_m .newest) := by
      refine ⟨fun x hx => (ho x hx).elim, ?_, ?_⟩
      · exact fun x hx => (ho x hx).elim
      · exact fun x hx => (ho x hx).elim
    exact ⟨o.val, (rr_truth_native_l I mn.2.1 (KP.ord0_m .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => o)).mpr ord,
      Or.inl (fun x hx => ho ⟨x, hx⟩),
      fun i l hi hl => (ne ⟨l, (height l).mpr ⟨i, hi, hl⟩⟩).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原生高度界下的全部旧前驱更新

实际有限历史先构造 Ic_bound。支撑高于此界的下一共同层同时更新所有旧行，
原生共同层、全局缺失和工作侧方块均由同一个复合图保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 在施加下一扩展器之前，原生历史界已经保证全部工作支撑严格增长。
只需新支撑的实际像是序数；不依赖尚未构造的新后继或相邻共同层。 -/
theorem Ic_history_d.support_lt_l
    {ω T Q G E L m H S Q' G' n N R B σ u U β c χ ρ ψ
      i X A π z Z α μ φ : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L m H S Q' G')
    (hω : M.IsOmega ω) (qf : M.IsSetFunction I Q) (lf : M.IsSetFunction I L)
    (top : Ic_at_d H n N B σ u U β) (qc : Rd_entry_d n c Q) (mn : Smdl_d I c N R)
    (bound : Ic_bound_d I H Q N R σ n χ)
    (next : Rd_entry_d ρ ψ σ) (ordinal : M.IsOrdinal ψ) (above : Rd_entry_d χ ρ R)
    (old : Ic_at_d H i X A π z Z α) (hi : M.mem i n)
    (support : Rd_entry_d i μ L) (image : Rd_entry_d μ φ π) : M.mem φ ψ := by
  obtain ⟨l,ν,V₁,V₂,D,t,c₁,c₂,R₁,R₂,qi,qn,mi,mn₂,same⟩ :=
    (hist.past i n X A π z Z α N B σ u U β old top hi).active_l (lf.2 i) support
  have eq := qf.2 n c₂ c qn qc
  subst c₂
  have eq := (smdl_unique_l I mn₂ mn).2
  subst R₂
  obtain ⟨_,_,_,row⟩ := hist.row_l hZF old
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,copy⟩ := row
  have eq := copy.1.1.1.2 μ ν φ same.left_end image
  subst ν
  obtain ⟨c₀,qc₀,_,row⟩ := hist.row_l hZF top
  have eq := qf.2 n c₀ c qc₀ qc
  subst c₀
  obtain ⟨R₀,S₀,_,b,_,_,mn₀,mb,_,_,_,_,_,_,map⟩ := row
  have eq := (smdl_unique_l I mn₀ mn).2
  subst R₀
  have height : Ic_height_d I H Q N R σ n i l :=
    ⟨same.right_ord_l hZF hω mn mb map,
      X,A,π,z,Z,α,B,u,U,β,c₁,c,R₁,μ,φ,V₁,V₂,D,t,old,top,qi,qc,mi,mn,same⟩
  obtain ⟨χ',_,hχ⟩ := map.1.1.2.2 χ (bound.ordinal.1 0)
  have high : M.mem χ' ψ :=
    ((mb.2 χ' ψ).mp ((map.relation_l I hZF hω mn mb.1 hχ next).mp above)).2.2
  rcases bound.upper i l hi height with low | eq
  · exact ordinal.transitive χ' high φ
      (((mb.2 φ χ').mp ((map.relation_l I hZF hω mn mb.1 same.right_end hχ).mp low)).2.2)
  · exact (map.1.1.1.2 χ χ' φ hχ (eq ▸ same.right_end)) ▸ high

/-- 当前原关系中的单一严格比较足以更新全部较早前驱。 -/
theorem Ic_history_d.past_extend_l
    {ω T Q G E L m H S Q' G' n N R B σ u U β c b C W D τ d μ ν ψ A V F t : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L m H S Q' G')
    (top : Ic_at_d H n N B σ u U β) (hω : M.IsOmega ω) (hm : M.SuccessorOf m n)
    (qf : M.IsSetFunction I Q) (qc : Rd_entry_d n c Q) (mn : Smdl_d I c N R)
    (bound : Ic_bound_d I H Q N R σ n b) (mc : Smdl_d I d C W)
    (ext : Extensional (smdl_structure_l I (R := W) mc.2.1))
    (qd : Rd_entry_d m d Q) (active : Rd_entry_d n μ L)
    (adjacent : Ic_agree_d I N R B σ C W D τ μ ν ψ A V F t) (above : Rd_entry_d b μ R) :
    ∀ i X P π z Z α, Ic_at_d H i X P π z Z α →
      Ic_past_d I Q L i m X P π C D τ ∧
      ∃ ρ l φ A₁ V₁ F₁ t₁ c₁ R₁, Rd_entry_d i c₁ Q ∧ Smdl_d I c₁ X R₁ ∧
        Ic_agree_d I X R₁ P π C W D τ ρ l φ A₁ V₁ F₁ t₁ ∧ (Rd_entry_d l ν W ∨ l = ν) := by
  let N₀ := smdl_structure_l I (R := R) mn.2.1
  obtain ⟨c₀, qc₀, _, row⟩ := hist.row_l hZF top
  have eq := qf.2 n c₀ c qc₀ qc
  subst c₀
  obtain ⟨R₀, RB, _, cb, _, _, mn₀, mb, _, _, _, _, _, _, map⟩ := row
  have eq := (smdl_unique_l I mn₀ mn).2
  subst R₀
  intro i X P π z Z α ai
  have hi := (hist.domain i).mpr (ai.imp fun _ h => h.1)
  rcases (hm i).mp hi with hin | eq
  · rcases hist.past i n X P π z Z α N B σ u U β ai top hin with
      ⟨c₁, qi, qn, ex, ep, eπ, no⟩ |
      ⟨k, ρ, l, φ, A₀, V₀, F₀, t₀, c₁, c₂, R₁, R₂, hik, hk, support, first, qi, qn, mx, my, previous⟩
    · subst X P π
      have eq := qf.2 n c₁ c qn qc
      subst c₁
      exact ⟨Or.inr ⟨n, μ, ν, ψ, A, V, F, t, c, d, R, W,
        Or.inr hin, hm.predecessor_mem, active, fun l hl => (no l hl).elim, qi, qd, mn, mc, adjacent⟩,
        μ, ν, ψ, A, V, F, t, c, R, qi, mn, adjacent, Or.inr rfl⟩
    · have eq := qf.2 n c₂ c qn qc
      subst c₂
      have eq := (smdl_unique_l I my mn).2
      subst R₂
      have height : Ic_height_d I H Q N R σ n i l :=
        ⟨previous.right_ord_l hZF hω mn mb map, X, P, π, z, Z, α, B, u, U, β,
          c₁, c, R₁, ρ, φ, A₀, V₀, F₀, t₀, ai, top, qi, qc, mx, mn, previous⟩
      have lt : Rd_entry_d l μ R := by
        rcases bound.upper i l hin height with lower | eq
        · have upper : N₀.IsLimitOrdinal ⟨μ, adjacent.common.left_rank.1⟩ :=
            (Formula.satisfies_isLimitOrdinal_iff ..).mp
              ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
                (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨μ, adjacent.common.left_rank.1⟩)).mp adjacent.common.limit)
          exact upper.1.transitive ⟨b, bound.ordinal.1 0⟩ above
            ⟨l, height.1.1 0⟩ lower
        · exact eq ▸ above
      obtain ⟨l', V', t', image, _, _, next⟩ := previous.trans_l hZF adjacent hω mn mc mb map ext lt
      have below := (adjacent.common.endpoint.2.2 l').mpr ⟨l, previous.common.right_rank.1, lt, image⟩
      exact ⟨Or.inr ⟨k, ρ, l', φ, A₀, V', F₀, t', c₁, d, R₁, W,
        hik, (hm k).mpr (Or.inl hk), support, first, qi, qd, mx, mc, next⟩,
        ρ, l', φ, A₀, V', F₀, t', c₁, R₁, qi, mx, next, Or.inl below⟩
  · have eq := hZF.1.eq_of_same_members i n eq
    subst i
    obtain ⟨eX, eP, eπ, _, _, _⟩ := ai.unique_l (ZF.modelsKP hZF) hist.function top
    subst X P π
    exact ⟨Or.inr ⟨n, μ, ν, ψ, A, V, F, t, c, d, R, W,
      Or.inl rfl, hm.predecessor_mem, active, fun _ _ => rfl, qc, qd, mn, mc, adjacent⟩,
      μ, ν, ψ, A, V, F, t, c, R, qc, mn, adjacent, Or.inr rfl⟩


end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际复制历史界的对象语言 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ic_bound_m {d} (H Q N R σ n b : Term d) : Formula 1 d := set[d] ⟪
  ⌜rr_ord_m⌝ₚ(⌜N⌝ₛ,⌜R⌝ₛ,⌜b⌝ₛ) ∧
  ((∀ x ∈ ⌜N⌝ₛ, ¬ ⌜rd_entry0_m⌝ₚ(x,⌜b⌝ₛ,⌜R⌝ₛ)) ∨
    (∃ i ∈ ⌜n⌝ₛ, ⌜ic_height_m⌝ₚ(⌜H⌝ₛ,⌜Q⌝ₛ,⌜N⌝ₛ,⌜R⌝ₛ,⌜σ⌝ₛ,⌜n⌝ₛ,i,⌜b⌝ₛ))) ∧
  (∀ i l, i ∈ ⌜n⌝ₛ → ⌜ic_height_m⌝ₚ(⌜H⌝ₛ,⌜Q⌝ₛ,⌜N⌝ₛ,⌜R⌝ₛ,⌜σ⌝ₛ,⌜n⌝ₛ,i,l) →
    ⌜rd_entry0_m⌝ₚ(l,⌜b⌝ₛ,⌜R⌝ₛ) ∨ l = ⌜b⌝ₛ)⟫
derive_free_closed ic_bound_m

theorem ic_bound_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (H Q N R σ n b : Term d) :
    Formula.satisfies ρ (ic_bound_m H Q N R σ n b) ↔
      Ic_bound_d (kp_pair_l hKP) (H.eval ρ) (Q.eval ρ) (N.eval ρ) (R.eval ρ) (σ.eval ρ) (n.eval ρ) (b.eval ρ) := by
  simp only [ic_bound_m,Formula.satisfies_conj_iff,rr_ord_sat_l (kp_pair_l hKP),
    Formula.satisfies_forallMem_iff,Formula.satisfies_neg_iff,rd_entry0_sat_l hKP.1,
    Formula.satisfies_disj_iff,Formula.satisfies_existsMem_iff,ic_height_sat_l hKP,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,Formula.satisfies_extensionalEq_iff_eq hKP.1,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c⟩ => ⟨a,b,c⟩,fun h => ⟨h.ordinal,h.origin,h.upper⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 已选原回合对实际复制历史的保持

原帧只记录当前节点、长度、四张树图、当前关系模型及历史界。
回合性质断言每份已有复制历史都沿这一次原回合延长；两种工厂证明该性质，
内部运行据此复制同一原对局，不预设分支选择或下一工作后继。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

-- n,m,T,Q,G,E,N,R,χ。
def Ic_frame_d (ω : M.Domain) (v : Fin 9 → M.Domain) (H S Q G : M.Domain) : Prop :=
  M.mem (v 0) ω ∧ ∃ Λ, M.IsSetFunction I Λ ∧
    (∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p (v 5) ∧ It_payload_d p κ ρ F) ∧
    Ic_history_d hZF ω (v 2) (v 3) (v 4) (v 5) Λ (v 1) H S Q G ∧
    ∃ A π z Z α, Ic_at_d H (v 0) (v 6) A π z Z α ∧ Ic_bound_d I H (v 3) (v 6) (v 7) π (v 0) (v 8)

def Ic_round_d (ω : M.Domain) (v w : Fin 9 → M.Domain) : Prop :=
  ∀ H S Q G, Ic_frame_d hZF ω v H S Q G →
    ∃ H' S' Q' G', Ic_frame_d hZF ω w H' S' Q' G' ∧
      M.MemberSubset H H' ∧ M.MemberSubset Q Q' ∧ M.MemberSubset G G'

theorem Ic_round_d.trans_l {ω : M.Domain} {v w z : Fin 9 → M.Domain}
    (first : Ic_round_d hZF ω v w) (second : Ic_round_d hZF ω w z) : Ic_round_d hZF ω v z := by
  intro H S Q G frame
  obtain ⟨H₁,S₁,Q₁,G₁,mid,hh,hq,hg⟩ := first H S Q G frame
  obtain ⟨H₂,S₂,Q₂,G₂,last,hh',hq',hg'⟩ := second H₁ S₁ Q₁ G₁ mid
  exact ⟨H₂,S₂,Q₂,G₂,last,fun x hx => hh' x (hh x hx),
    fun x hx => hq' x (hq x hx),fun x hx => hg' x (hg x hx)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 已选回合保持复制历史的对象语言

量词只遍历模型中的实际集合图。内部运行记录这一可分离性质，
随后以类依赖选择沿同一原运行构造相容的工作历史。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ic_frame_m {d} (ω : Term d) (v : Fin 9 → Term d) (H S Q G : Term d) : Formula 1 d := set[d] ⟪
  ⌜v 0⌝ₛ ∈ ⌜ω⌝ₛ ∧ (∃ Λ, ⌜Formula.isFunction kpair_convention_l⌝ₚ(Λ) ∧
    (∀ i ρ, ⌜rd_entry0_m⌝ₚ(i,ρ,Λ) ↔ ∃ p κ F,
      ⌜rd_entry0_m⌝ₚ(i,p,⌜v 5⌝ₛ) ∧ ⌜it_payload_m⌝ₚ(p,κ,ρ,F)) ∧
    ⌜ic_history_m⌝ₚ(⌜ω⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,⌜v 5⌝ₛ,Λ,⌜v 1⌝ₛ,⌜H⌝ₛ,⌜S⌝ₛ,⌜Q⌝ₛ,⌜G⌝ₛ) ∧
    (∃ A π z Z α, ⌜ic_at_m⌝ₚ(⌜H⌝ₛ,⌜v 0⌝ₛ,⌜v 6⌝ₛ,A,π,z,Z,α) ∧
      ⌜ic_bound_m⌝ₚ(⌜H⌝ₛ,⌜v 3⌝ₛ,⌜v 6⌝ₛ,⌜v 7⌝ₛ,π,⌜v 0⌝ₛ,⌜v 8⌝ₛ)))⟫

@[simp] theorem ic_frame_closed_l {d} (ω : Term d) (v : Fin 9 → Term d) (H S Q G : Term d)
    (hω : ω.freeSupport = []) (hv : ∀ i, (v i).freeSupport = [])
    (hH : H.freeSupport = []) (hS : S.freeSupport = []) (hQ : Q.freeSupport = []) (hG : G.freeSupport = []) :
    (ic_frame_m ω v H S Q G).FreeClosed := by
  simp -implicitDefEqProofs [ic_frame_m,Definitional.Formula.FreeClosed,hω,hv,hH,hS,hQ,hG]

theorem ic_frame_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d)
    (ω : Term d) (v : Fin 9 → Term d) (H S Q G : Term d) :
    Formula.satisfies ρ (ic_frame_m ω v H S Q G) ↔
      Ic_frame_d hZF (ω.eval ρ) (fun i => (v i).eval ρ) (H.eval ρ) (S.eval ρ) (Q.eval ρ) (G.eval ρ) := by
  simp only [ic_frame_m,Ic_frame_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_isFunction_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,rd_entry0_sat_l hZF.1,
    it_payload_sat_l hZF.1,ic_history_sat_l hZF,ic_at_sat_l hZF.1,ic_bound_sat_l (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

def ic_round_m {d} (ω : Term d) (v w : Fin 9 → Term d) : Formula 1 d :=
  let e : Term d → Term (4+d) := fun t => t.rename (Fin.natAdd 4)
  let u : Fin 4 → Term (4+d) := fun i => .bound (i.castAdd d)
  let e' : Term (4+d) → Term (4+(4+d)) := fun t => t.rename (Fin.natAdd 4)
  let z : Fin 4 → Term (4+(4+d)) := fun i => .bound (i.castAdd (4+d))
  rb_forall_m (.imp (ic_frame_m (e ω) (fun i => e (v i)) (u 0) (u 1) (u 2) (u 3))
    (rb_exists_m (n := 4) (.conj (ic_frame_m (e' (e ω)) (fun i => e' (e (w i))) (z 0) (z 1) (z 2) (z 3))
      (.conj (Formula.subset (e' (u 0)) (z 0))
        (.conj (Formula.subset (e' (u 2)) (z 2)) (Formula.subset (e' (u 3)) (z 3)))))))

@[simp] theorem ic_round_closed_l {d} (ω : Term d) (v w : Fin 9 → Term d)
    (hω : ω.freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) (hw : ∀ i, (w i).freeSupport = []) :
    (ic_round_m ω v w).FreeClosed := by
  simp -implicitDefEqProofs [ic_round_m,Definitional.Formula.FreeClosed,hω,hv,hw]

theorem ic_round_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω : Term d) (v w : Fin 9 → Term d) :
    Formula.satisfies ρ (ic_round_m ω v w) ↔
      Ic_round_d hZF (ω.eval ρ) (fun i => (v i).eval ρ) (fun i => (w i).eval ρ) := by
  simp only [ic_round_m,rb_forall_sat_l,rb_exists_sat_l,Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff,ic_frame_sat_l hZF,Formula.satisfies_subset_iff,
    Term.eval_bound,Fin.addCases_left,Definitional.Term.eval_rename,Env.reindex,Function.comp_def,Fin.addCases_right]
  constructor
  · intro h H S Q G frame
    obtain ⟨z,next,rows,codes,maps⟩ := h (fun i => [H,S,Q,G].get i) frame
    exact ⟨z 0,z 1,z 2,z 3,next,rows,codes,maps⟩
  · intro h u frame
    obtain ⟨H,S,Q,G,next,rows,codes,maps⟩ := h (u 0) (u 1) (u 2) (u 3) frame
    exact ⟨fun i => [H,S,Q,G].get i,next,rows,codes,maps⟩

end YesMetaZFC.SetTheory.LargeCardinal
