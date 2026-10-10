import YesMetaZFC.SetTheory.LargeCardinal.IterationRankValue

/-! # 从实际复制树构造整列移位下降高度

每个高度是根秩图的像在唯一联合节点处的值。替代收集全部内部自然数
上的值；任意严格树边都由联合尝试延伸和同一秩图的不等式给出严格下降。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.rank_l {ω T Q G E L H Q' G' U C ι o X₀ A₀ π₀ z₀ Z₀ α₀ a₀ S₀ B R η F : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G')
    (tree : It_diagram_d hZF ω ω T Q G) (en : Ja_enum_d I ω ω Q U)
    (start : Ic_at_d H o X₀ A₀ π₀ z₀ Z₀ α₀) (ho : ∀ x, ¬ M.mem x o)
    (first : Smem_d I a₀ A₀ S₀) (space : Ja_space_d I ω T Q G U A₀ S₀ o π₀ B R)
    (rank : Rr_d I B R η F) (hη : M.mem η Z₀) (hF : M.mem F Z₀)
    (hC : M.mem C Z₀) (hι : M.mem ι Z₀) (trans : M.TransitiveSet C) (inj : M.IsSetInjectionFromTo I ι C ω)
    (cover : ∀ i a X R, Rd_entry_d i a Q → KPair_d M a X R → M.MemberSubset X C)
    (hT : M.mem T Z₀) (hQ : M.mem Q Z₀) (hG : M.mem G Z₀) (hU : M.mem U Z₀)
    (hπ : M.mem π₀ Z₀) (hB : M.mem B Z₀) (hR : M.mem R Z₀) :
    ∃ D, M.IsSetFunction I D ∧ M.IsDomainOf I ω D ∧
      (∀ i δ, Rd_entry_d i δ D ↔ Jr_value_d I H G' T G U o F i δ) ∧
      (∀ i X A π z Z α δ, Ic_at_d H i X A π z Z α → Rd_entry_d i δ D →
        M.mem δ Z ∧ M.IsLimitOrdinal δ ∧ Sc_regular_d Z δ ∧
          ∃ g ε, It_map_d G' o i g ∧ Rd_entry_d η ε g ∧ M.mem ε δ) ∧
      ∀ k l g δ ε, It_map_d G' k l g → M.mem k l → Rd_entry_d k δ D → Rd_entry_d l ε D →
        ∃ γ, Rd_entry_d δ γ g ∧ M.mem ε γ := by
  have attempt {i X A π z Z α} (here : Ic_at_d H i X A π z Z α) :=
    hist.attempt_l hZF tree en start ho first space hC hι trans inj cover hT hQ hG hU hπ hB hR here
  have image {i X A π z Z α g F'} (here : Ic_at_d H i X A π z Z α)
      (hg : It_map_d G' o i g) (ff : Rd_entry_d F F' g) :
      ∃ B' R' η', Rd_entry_d B B' g ∧ Rd_entry_d R R' g ∧ Rd_entry_d η η' g ∧
        M.IsSetFunction I F' ∧ M.IsDomainOf I B' F' ∧
        (∀ s δ, Rd_entry_d s δ F' → M.IsLimitOrdinal δ ∧ Sc_regular_d Z δ ∧ M.mem η' δ) ∧
        ∀ s t δ ε, Rd_entry_d s t R' → Rd_entry_d s δ F' → Rd_entry_d t ε F' → M.mem δ ε := by
    obtain ⟨R₀, Rz, _, _, mz₀, mz, source, target, j⟩ := hist.embedding_l hZF start here hg
    obtain ⟨B', _, bb⟩ := j.1.1.2.2 B hB
    obtain ⟨R', _, rr⟩ := j.1.1.2.2 R hR
    obtain ⟨η', _, hh⟩ := j.1.1.2.2 η hη
    exact ⟨B', R', η', bb, rr, hh, rank.image_l hZF source.omega source.transitive target.transitive
      mz₀ mz j source.theory.algebra bb rr hh ff⟩
  have total i (hi : M.mem i ω) : ∃ δ, Jr_value_d I H G' T G U o F i δ := by
    obtain ⟨_, X, A, π, z, Z, α, here, _⟩ := hist.at_l hZF hi
    obtain ⟨g, a, S, q, B', R', P, s, hg, _, _, bb, _, _, pair, hs, node, values⟩ := attempt here
    obtain ⟨_, _, _, _, _, _, _, _, j⟩ := hist.embedding_l hZF start here hg
    obtain ⟨F', _, ff⟩ := j.1.1.2.2 F hF
    obtain ⟨B₁, _, _, bb₁, _, _, _, dom, _⟩ := image here hg ff
    have eq := j.1.1.1.2 B B₁ B' bb₁ bb
    subst B₁
    obtain ⟨δ, value⟩ := (dom s).mp hs
    exact ⟨δ, X, A, π, z, Z, α, g, F', P, s, here, hg, ff, node.lift_l hZF tree en values, pair, value⟩
  have unique i δ ε (h : Jr_value_d I H G' T G U o F i δ) (k : Jr_value_d I H G' T G U o F i ε) : δ = ε := by
    obtain ⟨X, A, π, z, Z, α, g, F', P, s, here, hg, ff, lift, pair, value⟩ := h
    obtain ⟨X₁, A₁, π₁, z₁, Z₁, α₁, g₁, F₁, P₁, s₁, here₁, hg₁, ff₁, lift₁, pair₁, value₁⟩ := k
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := here₁.unique_l (ZF.modelsKP hZF) hist.function here
    subst X₁ A₁ π₁ z₁ Z₁ α₁
    have eg := hist.diagram.map_unique_l hZF hg₁ hg
    subst g₁
    obtain ⟨_, _, _, _, _, _, _, _, j⟩ := hist.embedding_l hZF start here hg
    have ef := j.1.1.1.2 F F₁ F' ff₁ ff
    subst F₁
    have ep := lift₁.unique_l (ZF.modelsKP hZF) lift
    subst P₁
    have es := kpair_unique_l M hZF.1 pair₁ pair
    subst s₁
    obtain ⟨_, _, _, _, _, _, fn, _⟩ := image here hg ff
    exact fn.2 s δ ε value value₁
  let ρ : Env M 7 := ⟨Fin.cases F (Fin.cases o (Fin.cases U (Fin.cases G
    (Fin.cases T (Fin.cases G' (fun _ => H)))))), fun _ => F⟩
  let φ : BinarySchema 7 := {
    body := jr_value_m (.bound 8) (.bound 7) (.bound 6) (.bound 5)
      (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have read i δ : φ.denote ρ i δ ↔ Jr_value_d I H G' T G U o F i δ := jr_value_sat_l I hZF.1 ..
  obtain ⟨V, vs⟩ := ZF.exists_functionalImage hZF φ ρ ω
    (fun i hi => (total i hi).imp fun δ hd => (read i δ).mpr hd)
    (fun i δ ε hd he => unique i δ ε ((read i δ).mp hd) ((read i ε).mp he))
  obtain ⟨D, df, ds⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun i hi => (total i hi).imp fun δ hd => (read i δ).mpr hd)
    (fun i _ δ ε hd he => unique i δ ε ((read i δ).mp hd) ((read i ε).mp he))
    (fun i δ hi hd => (vs δ).mpr ⟨i, hi, hd⟩)
  have spec i δ : Rd_entry_d i δ D ↔ Jr_value_d I H G' T G U o F i δ := (ds i δ).trans
    ⟨fun h => (read i δ).mp h.2, fun h => ⟨by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨r, hr, _⟩, _⟩ := h
      exact (hist.domain i).mpr ⟨r, hr⟩, (read i δ).mpr h⟩⟩
  refine ⟨D, df.1, df.2.1, spec, ?_, ?_⟩
  · intro i X A π z Z α δ here hd
    obtain ⟨X₁, A₁, π₁, z₁, Z₁, α₁, g, F', P, s, here₁, hg, ff, _, _, value⟩ := (spec i δ).mp hd
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := here₁.unique_l (ZF.modelsKP hZF) hist.function here
    subst X₁ A₁ π₁ z₁ Z₁ α₁
    obtain ⟨_, _, _, _, _, _, _, target, j⟩ := hist.embedding_l hZF start here hg
    obtain ⟨_, _, η', _, _, hh, _, _, regular, _⟩ := image here hg ff
    obtain ⟨limit, reg, above⟩ := regular s δ value
    exact ⟨(rd_entry_transitive_l target.transitive (j.1.1.output_mem_of_pairMember ff) value).2,
      limit, reg, g, η', hg, hh, above⟩
  · intro k l g δ ε edge lt hd he
    obtain ⟨X, A, π, z, Z, α, f, Fk, Pk, s, left, hf, ff, lift, pair, value⟩ := (spec k δ).mp hd
    obtain ⟨Y, B₁, σ, v, V, β, h, Fl, Pl, t, right, hh, fh, lift', pair', value'⟩ := (spec l ε).mp he
    obtain ⟨f₀, _, Sk, qk, Bk, Rk, P₀, s₀, hf₀, _, _, bk, _, _, ps₀, hs, node, values⟩ := attempt left
    have eq := hist.diagram.map_unique_l hZF hf₀ hf
    subst f₀
    have eq := (node.lift_l hZF tree en values).unique_l (ZF.modelsKP hZF) lift
    subst P₀
    have eq := kpair_unique_l M hZF.1 ps₀ pair
    subst s₀
    obtain ⟨h₀, _, Sl, ql, Bl, Rl, P₁, t₀, hh₀, _, _, bl, rl, space', pt₀, _, next, later⟩ := attempt right
    have eq := hist.diagram.map_unique_l hZF hh₀ hh
    subst h₀
    have eq := (next.lift_l hZF tree en later).unique_l (ZF.modelsKP hZF) lift'
    subst P₁
    have eq := kpair_unique_l M hZF.1 pt₀ pair'
    subst t₀
    obtain ⟨_, Rz, _, _, _, mz, _, source, jf⟩ := hist.embedding_l hZF start left hf
    obtain ⟨_, Rv, _, _, _, mv, _, target, jh⟩ := hist.embedding_l hZF start right hh
    obtain ⟨_, _, hz, _⟩ := hist.row_l hZF left
    obtain ⟨_, _, hv, _⟩ := hist.row_l hZF right
    have j := hist.diagram.elementary k l g z Z Rz v V Rv edge hz hv mz.1 mv.1
    have cross x a b (ha : Rd_entry_d x a f) (hb : Rd_entry_d x b h) : Rd_entry_d a b g := by
      obtain ⟨b', _, hab⟩ := j.1.1.2.2 a (jf.1.1.output_mem_of_pairMember ha)
      exact jh.1.1.1.2 x b' b (hist.diagram.comp o k l f g h hf edge hh x a b' ha hab) hb ▸ hab
    obtain ⟨u, su, tu⟩ := hist.attempt_extend_l hZF tree en left right edge lt node next values later pair pair' hs (cross B Bk Bl bk bl) space'
    have hδ := (rd_entry_transitive_l source.transitive (jf.1.1.output_mem_of_pairMember ff) value).2
    obtain ⟨γ, _, dg⟩ := j.1.1.2.2 δ hδ
    have ug := (j.entry_l hZF source.omega source.transitive target.transitive mz mv su dg (cross F Fk Fl ff fh)).mp value
    obtain ⟨_, R₁, _, _, rr, _, _, _, _, decrease⟩ := image right hh fh
    have eq := jh.1.1.1.2 R R₁ Rl rr rl
    subst R₁
    exact ⟨γ, dg, decrease t u ε γ tu value' ug⟩

end YesMetaZFC.SetTheory.LargeCardinal
