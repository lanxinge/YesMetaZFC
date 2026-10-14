import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyRank
import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyTree
import YesMetaZFC.SetTheory.LargeCardinal.IterationCutHistory

/-! # 移位高度给出完整 nice 树的实际秩段

每个移位高度严格超过原目标秩段高度的像，故新秩段包含所属扩展器和
支撑。相对层级唯一性使结构码列可由替代收集；根高度保留背景正则性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

private def Jr_cut_d (ω H D i a : M.Domain) : Prop := ∃ X A π z Z α δ V S,
  Ic_at_d H i X A π z Z α ∧ Rd_entry_d i δ D ∧ Smem_d I a V S ∧
    M.mem V Z ∧ Vr_d Z δ V ∧ M.mem ω V ∧ M.MemberSubset A V

private def jr_cut_m {d} (ω H D i a : Term d) : Formula 1 d := set[d] ⟪
  ∃ X A π z Z α δ V S, ⌜ic_at_m⌝ₚ(⌜H⌝ₛ, ⌜i⌝ₛ, X, A, π, z, Z, α) ∧
    ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, δ, ⌜D⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜a⌝ₛ, V, S) ∧
    V ∈ Z ∧ ⌜pn_rank_m⌝ₚ(Z, δ, V) ∧ ⌜ω⌝ₛ ∈ V ∧ A ⊆ V⟫
derive_free_closed jr_cut_m

private theorem jr_cut_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω H D i a : Term d) :
    Formula.satisfies ρ (jr_cut_m ω H D i a) ↔
      Jr_cut_d I (ω.eval ρ) (H.eval ρ) (D.eval ρ) (i.eval ρ) (a.eval ρ) := by
  simp only [jr_cut_m, Jr_cut_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ic_at_sat_l hKP.1, rd_entry0_sat_l hKP.1, smem_sat_l I, Formula.satisfies_mem_iff,
    pn_rank_sat_l hKP, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.rank_cut_l {ω c T Q G E L H Q' G' U C ι o X₀ A₀ π₀ z₀ Z₀ α₀ a₀ S₀ B R F : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G')
    (nice : It_pnice_d hZF ω c ω T Q G E L) (en : Ja_enum_d J ω ω Q U)
    (start : Ic_at_d H o X₀ A₀ π₀ z₀ Z₀ α₀) (ho : ∀ x, ¬ M.mem x o)
    (first : Smem_d J a₀ A₀ S₀) (space : Ja_space_d J ω T Q G U A₀ S₀ o π₀ B R)
    (rank : Rr_d J B R α₀ F) (hα : M.mem α₀ Z₀) (hF : M.mem F Z₀)
    (hC : M.mem C Z₀) (hι : M.mem ι Z₀) (trans : M.TransitiveSet C) (inj : M.IsSetInjectionFromTo J ι C ω)
    (cover : ∀ i a X R, Rd_entry_d i a Q → KPair_d M a X R → M.MemberSubset X C)
    (hT : M.mem T Z₀) (hQ : M.mem Q Z₀) (hG : M.mem G Z₀) (hU : M.mem U Z₀)
    (hπ : M.mem π₀ Z₀) (hB : M.mem B Z₀) (hR : M.mem R Z₀) :
    ∃ E' L' D N, It_pnice_d hZF ω z₀ ω T Q' G' E' L' ∧ It_cut_d hZF ω ω Q' E' D N ∧
      (∀ δ, Rd_entry_d o δ D → M.IsRegularCardinal J δ ∧ M.mem α₀ δ) ∧
      (∀ i p, Rd_entry_d i p E' → (∀ x, ¬ M.mem x p) → Rd_entry_d i p E) ∧
      ∀ k l g δ ε, It_map_d G' k l g → M.mem k l → Rd_entry_d k δ D → Rd_entry_d l ε D →
        ∃ γ, Rd_entry_d δ γ g ∧ M.mem ε γ := by
  obtain ⟨D, df, dom, values, heights, drop⟩ := hist.rank_l hZF nice.tree.diagram en start ho first space rank
    hα hF hC hι trans inj cover hT hQ hG hU hπ hB hR
  obtain ⟨E', L', copied, moves⟩ := hist.nice_l hZF nice ho start
  obtain ⟨_, _, _, row₀⟩ := hist.row_l hZF start
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rank₀, _, _⟩ := row₀
  have contains {i X A π z Z α δ V} (here : Ic_at_d H i X A π z Z α) (hd : Rd_entry_d i δ D)
      (hV : M.mem V Z) (rv : Vr_d Z δ V) : M.MemberSubset A V := by
    obtain ⟨_, limit, _, g, ε, hg, he, below⟩ := heights i X A π z Z α δ here hd
    obtain ⟨_, _, _, _, mz₀, mz, source, target, j⟩ := hist.embedding_l hZF start here hg
    have aa := hist.cuts o i X₀ A₀ π₀ z₀ Z₀ α₀ X A π z Z α g start here hg
    have ra := (j.hierarchy_l hZF source.omega source.transitive target.transitive mz₀ mz he aa).mp rank₀
    exact (rv.compare_l hZF target.transitive hV (j.1.1.output_mem_of_pairMember aa) ra
      (limit.1.transitive ε below)).1
  have total i (hi : M.mem i ω) : ∃ a, Jr_cut_d J ω H D i a := by
    obtain ⟨_, X, A, π, z, Z, α, here, _, _, row⟩ := hist.at_l hZF hi
    obtain ⟨δ, hd⟩ := (dom i).mp hi
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, small, full, _⟩ := row
    obtain ⟨hδ, limit, _⟩ := heights i X A π z Z α δ here hd
    obtain ⟨V, hV, rv⟩ := full.hierarchy δ hδ limit.1
    have sub := contains here hd hV rv
    have hw := sub ω small.omega_mem
    obtain ⟨a, S, ma⟩ := smdl_membership_l J hZF ⟨ω, hw⟩
    exact ⟨a, X, A, π, z, Z, α, δ, V, S, here, hd, ma, hV, rv, hw, sub⟩
  have unique i a b (ha : Jr_cut_d J ω H D i a) (hb : Jr_cut_d J ω H D i b) : a = b := by
    obtain ⟨X, A, π, z, Z, α, δ, V, S, here, hd, ma, hV, rv, _⟩ := ha
    obtain ⟨X₁, A₁, π₁, z₁, Z₁, α₁, δ₁, V₁, S₁, here₁, hd₁, mb, hV₁, rv₁, _⟩ := hb
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := here₁.unique_l (ZF.modelsKP hZF) hist.function here
    subst X₁ A₁ π₁ z₁ Z₁ α₁
    have eq := df.2 i δ₁ δ hd₁ hd
    subst δ₁
    obtain ⟨_, _, _, row⟩ := hist.row_l hZF here
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, full, _⟩ := row
    have eq := rv₁.unique_l hZF full.source.transitive hV₁ hV rv
    subst V₁
    exact (smem_unique_l J hZF.1 ma mb).1
  let ρ : Env M 3 := ⟨Fin.cases D (Fin.cases H (fun _ => ω)), fun _ => ω⟩
  let φ : BinarySchema 3 := { body := jr_cut_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have read i a : φ.denote ρ i a ↔ Jr_cut_d J ω H D i a := jr_cut_sat_l J (ZF.modelsKP hZF) ..
  obtain ⟨V, vs⟩ := ZF.exists_functionalImage hZF φ ρ ω
    (fun i hi => (total i hi).imp fun a ha => (read i a).mpr ha)
    (fun i a b ha hb => unique i a b ((read i a).mp ha) ((read i b).mp hb))
  obtain ⟨N, nf, ns⟩ := ZF.exists_setFunctionFromTo_of_denote hZF J φ ρ
    (fun i hi => (total i hi).imp fun a ha => (read i a).mpr ha)
    (fun i _ a b ha hb => unique i a b ((read i a).mp ha) ((read i b).mp hb))
    (fun i a hi ha => (vs a).mpr ⟨i, hi, ha⟩)
  have cut i a (ha : Rd_entry_d i a N) := (read i a).mp ((ns i a).mp ha).2
  refine ⟨E', L', D, N, copied, ⟨df, dom, nf.1, nf.2.1, ?_, ?_, ?_⟩, ?_, ?_, drop⟩
  · intro i z a δ Z R hz ha hd mz
    obtain ⟨X, A, π, z₁, Z₁, α, δ₁, V, S, here, hd₁, ma, hV, rv, hw, _⟩ := cut i a ha
    obtain ⟨_, _, hz₁, row⟩ := hist.row_l hZF here
    have eq := hist.diagram.model_function.2 i z₁ z hz₁ hz
    subst z₁
    obtain ⟨_, _, _, _, _, _, _, _, _, mz₁, _⟩ := row
    obtain ⟨ez, _⟩ := smdl_unique_l J mz₁.1 mz.1
    subst Z₁
    have eq := df.2 i δ₁ δ hd₁ hd
    subst δ₁
    exact ⟨V, S, ma, hV, rv, (heights i X A π z Z α δ here hd).2.2.1, hw⟩
  · intro i p κ ρ F a V S hp pay ha ma
    obtain ⟨X, A, π, z, Z, α, p₀, κ₀, ρ₀, F₀, κ₁, ρ₁, F₁, here, _, _, _, hρ, hF, pay₁⟩ := ((moves i p).mp hp).active_l pay
    obtain ⟨e₁, e₂, e₃⟩ := pay₁.unique_l pay
    subst κ₁ ρ₁ F₁
    obtain ⟨X₁, A₁, π₁, z₁, Z₁, α₁, _, V₁, _, here₁, _, ma₁, _, _, _, sub⟩ := cut i a ha
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := here₁.unique_l (ZF.modelsKP hZF) hist.function here
    subst X₁ A₁ π₁ z₁ Z₁ α₁
    obtain ⟨eq, _⟩ := smdl_unique_l J ma₁.1 ma.1
    subst V₁
    obtain ⟨_, _, _, row⟩ := hist.row_l hZF here
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, pi⟩ := row
    exact ⟨sub ρ (pi.1.1.output_mem_of_pairMember hρ), sub F (pi.1.1.output_mem_of_pairMember hF)⟩
  · intro i j p κ ρ F a V S succ hp pay ha ma
    obtain ⟨X, A, π, z, Z, α, p₀, κ₀, ρ₀, F₀, κ₁, ρ₁, F₁, ai, hp₀, pay₀, _, hρ, _, pay₁⟩ := ((moves i p).mp hp).active_l pay
    have eq := (pay₁.unique_l pay).2.1
    subst ρ₁
    obtain ⟨Y, B, σ, u, U, β, _, V₁, _, aj, _, ma₁, _, _, _, sub⟩ := cut j a ha
    obtain ⟨eq, _⟩ := smdl_unique_l J ma₁.1 ma.1
    subst V₁
    obtain ⟨φ, same, _⟩ := (hist.past i j X A π z Z α Y B σ u U β ai aj succ.predecessor_mem).active_l
      (ZF.modelsKP hZF) nice.function ((nice.levels i ρ₀).mpr ⟨p₀, κ₀, F₀, hp₀, pay₀⟩)
    obtain ⟨_, _, _, row⟩ := hist.row_l hZF ai
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ep⟩ := row
    have eq := ep.1.1.1.2 ρ₀ φ ρ same.left_end hρ
    subst φ
    obtain ⟨_, _, _, row'⟩ := hist.row_l hZF aj
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, es⟩ := row'
    exact sub ρ (es.1.1.output_mem_of_pairMember same.right_end)
  · intro δ hd
    obtain ⟨_, _, _, _, _, _, g, F', _, s, _, hg, ff, _, _, value⟩ := (values o δ).mp hd
    have eq := hist.diagram.identity o g hg F F' ff
    exact rank.regular s δ (eq.symm ▸ value)
  · intro i p hp empty
    rcases (moves i p).mp hp with ⟨hp, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r, ⟨u, v, _, _, pair⟩, _⟩
    · exact hp
    · exact (empty u ((pair u).mpr (Or.inl rfl))).elim

end YesMetaZFC.SetTheory.LargeCardinal
