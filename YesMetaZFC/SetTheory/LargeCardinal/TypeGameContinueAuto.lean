import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContinue
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContinueSeed
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlCard

/-! # 原已发出请求自动完成继续轮

旧轮和当前请求确定完整伸展输入。实际源按旧回答域重定基，原武丁公式给出
当前正则性；随后直接调用两条真实树边的构造，调用方无需提供继续 seed。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.continue_tree_l {ω X η C Y η₀ C₀ μ μ₀ K K₀ R S c₀ α ξ T J G E H
    k c d o π π₀ Cᵣ γ Z₀ ζ V H₀ Lᵣ Vᵣ qᵣ : M.Domain}
    (context : Tg_context_d ω X η C) (prior : Tg_context_d ω Y η₀ C₀)
    (owner : Ic_model_d hZF ω μ K X R) (source : Ic_model_d hZF ω μ₀ K₀ Y S)
    (nc : Nonempty {x // M.mem x C}) (nc₀ : Nonempty {x // M.mem x C₀})
    (ρ₀ : Env (rt_model_l C₀ nc₀) 54) (old : Formula.satisfies ρ₀ tg_round0_m) (hw₀ : (ρ₀.bound 16).val = ω)
    (tree : It_pnice_d hZF ω c₀ α T J G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c J) (hd : Rd_entry_d k d J) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (ho : ∀ x, ¬ M.mem x o) (root : It_map_d G o ξ π) (root₀ : It_map_d G o k π₀)
    (iRoot : Rd_entry_d Cᵣ C π) (iRoot₀ : Rd_entry_d Cᵣ C₀ π₀)
    (anchor : Tg_anchor_d γ Z₀ X π) (priorAnchor : Tg_anchor_d γ Z₀ Y π₀)
    (lower : M.MemberSubset γ (ρ₀.bound 15).val) (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z₀)
    (ι : Env (rt_model_l C nc) 46) (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val = ω)
    (ne : ι.bound 23 ≠ ι.bound 1) (letters : M.mem (ι.bound 6).val Z₀)
    (row : Tg_past_at_d H₀ (ι.bound 22).val k Y S μ₀ K₀ η₀ C₀ Lᵣ Vᵣ qᵣ)
    (code : Tg_saved_code_d ω Vᵣ qᵣ (fun i => (ρ₀.bound i).val))
    (trace : Tg_trace_d ω C (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val (ι.bound 22).val
      (ι.bound 20).val (ρ₀.bound 41).val (ρ₀.bound 15).val (ρ₀.bound 11).val)
    (hV : M.mem V X) (rank : Vr_d X ζ V) (hV' : M.mem V Y) (rank' : Vr_d Y ζ V)
    (hζ : M.IsLimitOrdinal ζ) (hVC : M.mem V C₀) (hζδ : M.mem ζ (ι.bound 5).val)
    (hκV : M.mem (ρ₀.bound 15).val V) (hU : M.mem (ρ₀.bound 13).val V)
    (hD : M.mem (ρ₀.bound 12).val V) (hu : M.mem (ρ₀.bound 11).val V)
    (above : ∀ i ν, Rd_entry_d i ν H → M.mem ν (ι.bound 24).val) :
    ∃ ρ : Env (rt_model_l C nc) 28, Formula.satisfies ρ tc_seed0_m ∧
      (∀ i : Fin 10, (ρ.bound ([0, 1, 3, 4, 5, 6, 17, 18, 19, 20].get i)).val =
        (ρ₀.bound ([16, 15, 24, 14, 13, 12, 6, 5, 4, 3].get i)).val) ∧
      (ρ.bound 7).val = (ρ₀.bound 11).val ∧ ρ.bound 3 = ι.bound 27 ∧
      (∀ i : Fin 14, ρ.bound ([0, 2, 8, 9, 13, 14, 16, 21, 22, 23, 24, 25, 26, 27].get i) =
        ι.bound ([0, 5, 24, 28, 25, 36, 37, 38, 39, 40, 41, 42, 43, 44].get i)) ∧
      Tg_tree_step_d hZF ω X η c₀ α ξ T J G E c o Cᵣ γ Z₀ H₀ nc ι := by
  have fs := (context.read_l hZF owner.source).1
  have ft := (prior.read_l hZF source.source).1
  let P := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have state := (tg_issued_sat_l P ext ι).mp issued
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
  have card : Sc_inaccessible_d ω X (ι.bound 5).val :=
    context.control_card_l hZF owner.source nc _ state.control hw
  have δlimit := card.limit_l (ZF.modelsKP hZF) owner.source.transitive owner.source.theory.algebra.pair
  have δregular := (owner.inaccessible _ card).1
  obtain ⟨oldSeed, oldBody⟩ := (Formula.satisfies_conj_iff ..).mp old
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at oldSeed
  have empty₀ := (Formula.satisfies_isEmpty_iff ..).mp oldSeed.2.1
  have empty := (Formula.satisfies_isEmpty_iff ..).mp rules.2.1
  have he : (ι.bound 1).val = (ρ₀.bound 17).val := hZF.1.eq_of_same_members _ _ (fun x =>
    iff_of_false (fun hx => empty ⟨x, fs.transitive _ (ι.bound 1).property x hx⟩ hx)
      (fun hx => empty₀ ⟨x, ft.transitive _ (ρ₀.bound 17).property x hx⟩ hx))
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at oldBody
  have language := oldBody.2.2.2.2.2.2.1
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_m, Formula.satisfies_conj_iff] at language
  have τlimit := (rt_limit_l ft.transitive nc₀ (ZF.modelsKP hZF) (ρ₀.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have ωτ := owner.source.omega.subset_limitOrdinal hZF τlimit
  have hτX := owner.source.transitive V hV _ hκV
  have hτY := source.source.transitive V hV' _ hκV
  obtain ⟨K', owner'⟩ := owner.rebase_l hZF hτX ωτ
    (sc_ordinal_small_l hZF owner.source.omega owner.source.transitive mx owner.source.theory hτX τlimit.1)
  obtain ⟨K₁, source'⟩ := source.rebase_l hZF hτY ωτ
    (sc_ordinal_small_l hZF source.source.omega source.source.transitive my source.source.theory hτY τlimit.1)
  have hωV := rank.subset_mem_l owner.source.transitive hV hκV owner.source.omega_mem ωτ
  have hζC := fs.transitive _ (ι.bound 5).property ζ hζδ
  have hVC' := (context.rank.rank_l hZF owner.source.transitive context.member context.limit hζC hV rank).1
  obtain ⟨B, R₀, Kᵣ, mb, rootSource⟩ := tree.tree.sources o c₀ (tree.tree.root o ho)
  have j := tree.tree.diagram.elementary o k π₀ c₀ B R₀ d Y S root₀ (tree.tree.root o ho) hd mb.1 my.1
  have k' := tree.tree.diagram.elementary o ξ π c₀ B R₀ c X R root (tree.tree.root o ho) hc mb.1 mx.1
  obtain ⟨ρ, seed, oldEq, typeEq, arity, newEq⟩ := prior.continue_seed_l hZF nc₀ ρ₀ nc ι context source.source owner.source
    rootSource.transitive mb my mx j k' rootSource.omega_mem iRoot₀ iRoot
    hV' rank' hV rank hζ hωV hκV hVC' hw₀ old hw issued ne trace
  have h0 : (ρ.bound 0).val = ω := (oldEq 0).trans hw₀
  have h1 : (ρ.bound 1).val = (ρ₀.bound 15).val := oldEq 1
  have h3 : (ρ.bound 3).val = (ρ₀.bound 24).val := oldEq 2
  have h5 : (ρ.bound 5).val = (ρ₀.bound 13).val := oldEq 4
  have h6 : (ρ.bound 6).val = (ρ₀.bound 12).val := oldEq 5
  have h2 : (ρ.bound 2).val = (ι.bound 5).val := congrArg Subtype.val (newEq 1)
  have h8 : (ρ.bound 8).val = (ι.bound 24).val := congrArg Subtype.val (newEq 2)
  have links : ∀ i : Fin 6, (ι.bound ([0, 1, 27, 28, 24, 25].get i)).val =
      [ω, (ρ₀.bound 17).val, (ρ.bound 3).val, (ρ.bound 9).val, (ρ.bound 8).val, (ρ.bound 13).val].get i := by
    intro i
    exact Fin.cases hw (Fin.cases he (Fin.cases (congrArg Subtype.val arity.symm)
      (Fin.cases (congrArg Subtype.val (newEq 3).symm) (Fin.cases h8.symm
        (Fin.cases (congrArg Subtype.val (newEq 4).symm) (fun j => Fin.elim0 j)))))) i
  have lower' : M.MemberSubset γ (ρ.bound 1).val := h1.symm ▸ lower
  have δlimit' : M.IsLimitOrdinal (ρ.bound 2).val := h2.symm ▸ δlimit
  have δregular' : Sc_regular_d X (ρ.bound 2).val := h2.symm ▸ δregular
  have hζδ' : M.mem ζ (ρ.bound 2).val := h2.symm ▸ hζδ
  have hκV' : M.mem (ρ.bound 1).val V := h1.symm ▸ hκV
  have hU' : M.mem (ρ.bound 5).val V := h5.symm ▸ hU
  have hD' : M.mem (ρ.bound 6).val V := h6.symm ▸ hD
  have hu' : M.mem (ρ.bound 7).val V := typeEq.symm ▸ hu
  have above' : ∀ i ν, Rd_entry_d i ν H → M.mem ν (ρ.bound 8).val := fun i ν hn => h8.symm ▸ above i ν hn
  have codes : ∀ i : Fin 9, (ρ.bound ([14, 16, 21, 22, 23, 24, 25, 26, 27].get i)).val =
      (ι.bound ([36, 37, 38, 39, 40, 41, 42, 43, 44].get i)).val := by
    intro i
    exact Fin.cases (congrArg Subtype.val (newEq 5)) (Fin.cases (congrArg Subtype.val (newEq 6))
      (Fin.cases (congrArg Subtype.val (newEq 7)) (Fin.cases (congrArg Subtype.val (newEq 8))
        (Fin.cases (congrArg Subtype.val (newEq 9)) (Fin.cases (congrArg Subtype.val (newEq 10))
          (Fin.cases (congrArg Subtype.val (newEq 11)) (Fin.cases (congrArg Subtype.val (newEq 12))
            (Fin.cases (congrArg Subtype.val (newEq 13)) (fun j => Fin.elim0 j))))))))) i
  exact ⟨ρ, seed, oldEq, typeEq, arity, newEq,
    context.continue_image_tree_l hZFC nc ρ prior nc₀ ρ₀ old typeEq.symm h1.symm h3.symm h5.symm
      (h1.symm ▸ owner') (h1.symm ▸ source') tree succ hc hd mx my ho root root₀ iRoot iRoot₀ anchor priorAnchor
      lower' hγ hωZ ι issued ne row code links codes letters h0 δlimit' δregular'
      hV rank hV' rank' hζ hVC hζδ' hκV' hU' hD' hu' above' seed⟩

end YesMetaZFC.SetTheory.LargeCardinal
