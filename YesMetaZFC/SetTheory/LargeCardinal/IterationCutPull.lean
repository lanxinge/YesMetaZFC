import YesMetaZFC.SetTheory.LargeCardinal.IterationColumnPull
import YesMetaZFC.SetTheory.LargeCardinal.IterationCutHistory

/-! # 同一壳中的正则秩段列与严格下降回拉 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_cut_pull_l {ω B R b K U S u J C V π T Q Q' G' E E' A A' D D' : M.Domain}
    (sb : Ep_source_d hZF ω ω K B R) (su : Ep_source_d hZF ω ω J U S)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hC : M.mem C B) (ct : M.TransitiveSet C) (vt : M.TransitiveSet V) (hCV : Rd_entry_d C V π)
    (hQ : M.mem Q C) (hE : M.mem E C) (hA : M.mem A C) (hD : M.mem D C)
    (hQQ : Rd_entry_d Q Q' π) (hEE : Rd_entry_d E E' π) (hAA : Rd_entry_d A A' π) (hDD : Rd_entry_d D D' π)
    (diagram : It_diagram_d hZF ω ω T Q' G') (sources : ∀ i a, Rd_entry_d i a Q' → It_source_d hZF ω a)
    (cuts : It_cut_d hZF ω ω Q' E' A' D') : It_cut_d hZF ω ω Q E A D := by
  have hw := sb.omega
  have cb := sb.transitive C hC
  have nat := hj.natural_l hZF hw sb.transitive su.transitive mb mu sb.omega_mem
  have omega := hj.omega_l I hZF hw sb.transitive su.transitive mb mu sb.omega_mem
  have af := hj.column_l hZF hw sb.transitive su.transitive vt mb mu hCV omega hAA hA cuts.heights cuts.height_domain
  have df := hj.column_l hZF hw sb.transitive su.transitive vt mb mu hCV omega hDD hD cuts.codes cuts.code_domain
  have image {f g i x} (hf : M.mem f C) (hfg : Rd_entry_d f g π) (hi : M.mem i ω) (hx : Rd_entry_d i x f) :
      ∃ y, Rd_entry_d i y g ∧ Rd_entry_d x y π := by
    obtain ⟨y, _, hxy⟩ := hj.1.1.2.2 x (cb x (rd_entry_transitive_l ct hf hx).2)
    exact ⟨y, (hj.entry_l hZF hw sb.transitive su.transitive mb mu (nat i hi) hxy hfg).mp hx, hxy⟩
  have code {i a X P} (ha : Rd_entry_d i a D) (mx : Smem_d I a X P) :
      ∃ a' Y W, Rd_entry_d i a' D' ∧ Smem_d I a' Y W ∧ Rd_entry_d X Y π := by
    have hi := (df.bound_l ha).1
    obtain ⟨a', ha', haa⟩ := image hD hDD hi ha
    obtain ⟨q, hq⟩ := (diagram.model_domain i).mp hi
    obtain ⟨Y₀, W₀, _, my₀, _⟩ := sources i q hq
    obtain ⟨β, hβ⟩ := (cuts.height_domain i).mp hi
    obtain ⟨Y, W, my, _⟩ := cuts.ranks i q a' β Y₀ W₀ hq ha' hβ my₀
    obtain ⟨X₀, P₀, mx₀, hXY, _⟩ := ep_set_model_pull_l hZF sb su mb mu hj haa my
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx₀.1 mx.1
    exact ⟨a', Y, W, ha', my, hXY⟩
  refine ⟨(fn0_function_l (ZF.modelsKP hZF) af).1, (fn0_function_l (ZF.modelsKP hZF) af).2.1,
    (fn0_function_l (ZF.modelsKP hZF) df).1, (fn0_function_l (ZF.modelsKP hZF) df).2.1, ?_, ?_, ?_⟩
  · intro i q a β X P hq ha hβ mx
    have hi := (af.bound_l hβ).1
    obtain ⟨q', hq', hqq⟩ := image hQ hQQ hi hq
    obtain ⟨a', ha', haa⟩ := image hD hDD hi ha
    obtain ⟨β', hβ', hββ⟩ := image hA hAA hi hβ
    obtain ⟨Y, W, N, my, sy⟩ := sources i q' hq'
    obtain ⟨Z, H, mz, hZ, rank, reg, hzω⟩ := cuts.ranks i q' a' β' Y W hq' ha' hβ' my
    obtain ⟨X₀, P₀, _, σ, mx₀, sx, hXY, res, hs⟩ := ep_set_source_pull_l hZF sb su mb mu hj hqq my sy
    obtain ⟨ex, ep⟩ := smdl_unique_l I mx₀.1 mx.1
    subst X₀ P₀
    obtain ⟨Z₀, H₀, mz₀, hZZ, _⟩ := ep_set_model_pull_l hZF sb su mb mu hj haa mz
    have lift {x y} (hxy : Rd_entry_d x y π) (hy : M.mem y Y) :=
      (res.2 x y).mpr ⟨(hj.member_l I hZF hw mb mu hxy hXY).mpr hy, hxy⟩
    have hb := lift hββ (sy.rank_height_l hZF hZ rank reg hzω).1
    exact ⟨Z₀, H₀, mz₀, (hj.member_l I hZF hw mb mu hZZ hXY).mpr hZ,
      (hs.hierarchy_l hZF hw sx.transitive sy.transitive mx my hb (lift hZZ hZ)).mpr rank,
      (hs.regular_l hZF hw sx.transitive sy.transitive mx my hb).mpr reg,
      (hj.member_l I hZF hw mb mu omega hZZ).mpr hzω⟩
  · intro i p κ ρ F a X P hp pay ha mx
    have hi := (df.bound_l ha).1
    obtain ⟨p', hp', hpp⟩ := image hE hEE hi hp
    obtain ⟨a', Y, W, ha', my, hXY⟩ := code ha mx
    obtain ⟨r, pr, rf⟩ := pay
    have own := pr.mem_l M ct (rd_entry_transitive_l ct hE hp).2
    have own' := rf.mem_l M ct own.2
    obtain ⟨κ', _, hκ⟩ := hj.1.1.2.2 κ (cb κ own.1)
    obtain ⟨r', _, hr⟩ := hj.1.1.2.2 r (cb r own.2)
    obtain ⟨ρ', _, hρ⟩ := hj.1.1.2.2 ρ (cb ρ own'.1)
    obtain ⟨F', _, hF⟩ := hj.1.1.2.2 F (cb F own'.2)
    have pay' : It_payload_d p' κ' ρ' F' := ⟨r',
      (hj.kpair_l hZF hw sb.transitive su.transitive mb mu hpp hκ hr).mp pr,
      (hj.kpair_l hZF hw sb.transitive su.transitive mb mu hr hρ hF).mp rf⟩
    have h := cuts.contains i p' κ' ρ' F' a' Y W hp' pay' ha' my
    exact ⟨(hj.member_l I hZF hw mb mu hρ hXY).mpr h.1, (hj.member_l I hZF hw mb mu hF hXY).mpr h.2⟩
  · intro i j p κ ρ F a X P succ hp pay ha mx
    have hi := hw.transitive hZF j (df.bound_l ha).1 i succ.predecessor_mem
    obtain ⟨p', hp', hpp⟩ := image hE hEE hi hp
    obtain ⟨a', Y, W, ha', my, hXY⟩ := code ha mx
    obtain ⟨r, pr, rf⟩ := pay
    have own := pr.mem_l M ct (rd_entry_transitive_l ct hE hp).2
    have own' := rf.mem_l M ct own.2
    obtain ⟨κ', _, hκ⟩ := hj.1.1.2.2 κ (cb κ own.1)
    obtain ⟨r', _, hr⟩ := hj.1.1.2.2 r (cb r own.2)
    obtain ⟨ρ', _, hρ⟩ := hj.1.1.2.2 ρ (cb ρ own'.1)
    obtain ⟨F', _, hF⟩ := hj.1.1.2.2 F (cb F own'.2)
    have pay' : It_payload_d p' κ' ρ' F' := ⟨r',
      (hj.kpair_l hZF hw sb.transitive su.transitive mb mu hpp hκ hr).mp pr,
      (hj.kpair_l hZF hw sb.transitive su.transitive mb mu hr hρ hF).mp rf⟩
    have h := cuts.next i j p' κ' ρ' F' a' Y W succ hp' pay' ha' my
    exact (hj.member_l I hZF hw mb mu hρ hXY).mpr h

/-- 下降值属于给定边图所在的传递模型，故原存在见证也可回拉。 -/
theorem it_drop_pull_l {ω B R b U S u π G G' A A' : M.Domain}
    (hw : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hωB : M.mem ω B) (hGG : Rd_entry_d G G' π) (hAA : Rd_entry_d A A' π)
    (drop : ∀ k l g β γ, It_map_d G' k l g → M.mem k l → Rd_entry_d k β A' → Rd_entry_d l γ A' →
      ∃ ε, Rd_entry_d β ε g ∧ M.mem γ ε) :
    ∀ k l g β γ, It_map_d G k l g → M.mem k l → M.mem k ω → M.mem l ω →
      Rd_entry_d k β A → Rd_entry_d l γ A → ∃ ε, Rd_entry_d β ε g ∧ M.mem γ ε := by
  intro k l g β γ hg hkl hk hl hβ hγ
  have nat := hj.natural_l hZF hw bt ut mb mu hωB
  obtain ⟨r, pair, hr⟩ := hg
  have owned := rd_entry_transitive_l bt (hj.1.1.input_mem_of_pairMember hGG) hr
  have fixed := hj.fixed_pair_l hZF hw bt ut mb mu owned.1 pair (nat k hk) (nat l hl)
  obtain ⟨g', _, hgg⟩ := hj.1.1.2.2 g owned.2
  obtain ⟨β', _, hββ⟩ := hj.1.1.2.2 β (rd_entry_transitive_l bt (hj.1.1.input_mem_of_pairMember hAA) hβ).2
  obtain ⟨γ', _, hγγ⟩ := hj.1.1.2.2 γ (rd_entry_transitive_l bt (hj.1.1.input_mem_of_pairMember hAA) hγ).2
  have entry {x x' y y' f f'} (hx : Rd_entry_d x x' π) (hy : Rd_entry_d y y' π) (hf : Rd_entry_d f f' π) :=
    hj.entry_l hZF hw bt ut mb mu hx hy hf
  obtain ⟨ε', he, less⟩ := drop k l g' β' γ' ⟨r, pair, (entry fixed hgg hGG).mp hr⟩ hkl
    ((entry (nat k hk) hββ hAA).mp hβ) ((entry (nat l hl) hγγ hAA).mp hγ)
  have tr := hj.exists_delta_l hZF hw bt ut mb mu
    ((rd_entry0_m (.bound 3) (.newest : Term 4) (.bound 1)).conj (.mem (.bound 2) .newest))
    (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.conj (rd_entry0_delta_l ..) (.mem ..))
    ⟨Fin.cases g (Fin.cases γ (fun _ => β)), fun _ => β⟩
    ⟨Fin.cases g' (Fin.cases γ' (fun _ => β')), fun _ => β'⟩ (Fin.cases hgg (Fin.cases hγγ (fun _ => hββ)))
  simp only [Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff] at tr
  obtain ⟨ε, _, he, less⟩ := tr.mpr ⟨ε', (rd_entry_transitive_l ut (hj.1.1.output_mem_of_pairMember hgg) he).2, he, less⟩
  exact ⟨ε, he, less⟩

end YesMetaZFC.SetTheory.LargeCardinal
