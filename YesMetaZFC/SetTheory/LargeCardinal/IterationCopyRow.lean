import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyStep
import YesMetaZFC.SetTheory.LargeCardinal.IterationHistorySyntax

/-! # 整树复制的实际模型行

每行记录原模型、复制图、拥有目标秩段和完整可数闭工作模型。初等图只以
该秩段为目标；施加扩展器时，自动重选临界点字母表并使用完整工作模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ic_row_d (ω c X A π z Z α : M.Domain) : Prop := ∃ R S V a K K' K'',
  Smem_d I c X R ∧ Smem_d I a A S ∧ Smem_d I z Z V ∧
    Ep_source_d hZF ω ω K X R ∧ Ep_source_d hZF ω ω K' A S ∧ Ic_model_d hZF ω ω K'' Z V ∧
    M.mem A Z ∧ Vr_d Z α A ∧ M.IsLimitOrdinal α ∧ Smap_d I ω c a X A π

def ic_row_m {d} (ω c X A π z Z α : Term d) : Formula 1 d := set[d] ⟪
  ∃ R S V a K K' K'', ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, ⌜X⌝ₛ, R) ∧
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(a, ⌜A⌝ₛ, S) ∧
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜z⌝ₛ, ⌜Z⌝ₛ, V) ∧ ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, K, ⌜X⌝ₛ, R) ∧
    ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, K', ⌜A⌝ₛ, S) ∧ ⌜ic_model_m⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, K'', ⌜Z⌝ₛ, V) ∧
    ⌜A⌝ₛ ∈ ⌜Z⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜Z⌝ₛ, ⌜α⌝ₛ, ⌜A⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜α⌝ₛ) ∧
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, a, ⌜X⌝ₛ, ⌜A⌝ₛ, ⌜π⌝ₛ)⟫
derive_free_closed ic_row_m

theorem ic_row_sat_l {d} (η : Env M d) (ω c X A π z Z α : Term d) :
    Formula.satisfies η (ic_row_m ω c X A π z Z α) ↔
      Ic_row_d hZF (ω.eval η) (c.eval η) (X.eval η) (A.eval η) (π.eval η) (z.eval η) (Z.eval η) (α.eval η) := by
  simp only [ic_row_m, Ic_row_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isLimitOrdinal_iff, smem_sat_l I,
    ep_source_sat_l hZF, ic_model_sat_l hZF, pn_rank_sat_l (ZF.modelsKP hZF), smap_sat_l I hZF.1,
    Definitional.Term.eval_weaken]; rfl

/-- 同一行可在任意实际临界点重新读取，不加强原模型的数学前提。 -/
theorem Ic_row_d.rebase_l {ω c X A π z Z α κ κ' : M.Domain} (row : Ic_row_d hZF ω c X A π z Z α)
    (hκ : M.IsOrdinal κ) (below : M.MemberSubset ω κ) (image : Rd_entry_d κ κ' π) :
    ∃ R S V a K K' K'', Smem_d I c X R ∧ Smem_d I a A S ∧ Smem_d I z Z V ∧
      Ep_source_d hZF ω κ K X R ∧ Ep_source_d hZF ω κ' K' A S ∧ Ic_model_d hZF ω κ' K'' Z V ∧
      M.mem A Z ∧ Vr_d Z α A ∧ M.IsLimitOrdinal α ∧ Smap_d I ω c a X A π := by
  obtain ⟨R, S, V, a, _, _, _, hm, ha, hz, source, small, ambient, hA, rank, limit, hp⟩ := row
  have hκX := hp.1.1.input_mem_of_pairMember image
  have hκA := hp.1.1.output_mem_of_pairMember image
  have ord := hp.ordinal_l hZF source.omega source.transitive small.transitive hm ha image hκ
  have low := (hp.subset_l hZF source.omega source.transitive small.transitive hm ha
    (hp.omega_l I hZF source.omega source.transitive small.transitive hm ha source.omega_mem) image).mp below
  obtain ⟨K, sx⟩ := source.rebase_l hZF hκX below (sc_ordinal_small_l hZF source.omega source.transitive hm source.theory hκX hκ)
  obtain ⟨K', sa⟩ := small.rebase_l hZF hκA low (sc_ordinal_small_l hZF source.omega small.transitive ha small.theory hκA ord)
  obtain ⟨K'', sz⟩ := ambient.rebase_l hZF (ambient.source.transitive A hA κ' hκA) low
    (sc_ordinal_small_l hZF source.omega ambient.source.transitive hz ambient.source.theory
      (ambient.source.transitive A hA κ' hκA) ord)
  exact ⟨R, S, V, a, K, K', K'', hm, ha, hz, sx, sa, sz, hA, rank, limit, hp⟩

end
variable (hZFC : M.Models ZFC)
local notation "I" => kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))

/-- 正规外层容纳给定目标秩段，原嵌入直接成为首行。 -/
theorem ic_initial_row_l {ω δ Z α A X R c a S π K : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω ω K X R)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (ha : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) a A S)
    (hp : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c a X A π)
    (above : M.mem ω δ) (regular : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (outer : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ Z)
    (hA : M.mem A Z) (rank : Vr_d Z α A) (limit : M.IsLimitOrdinal α) :
    ∃ z, Ic_row_d (ZFC.models_zf_l hZFC) ω c X A π z Z α := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨K₀, V, ambient⟩ := ic_regular_model_l hZFC source.omega above regular outer
  obtain ⟨z, hz⟩ := ambient.source.code
  have ht := rank.transitive_l hZF ambient.source.transitive hA
  have hw := hp.omega_l (kp_pair_l (ZF.modelsKP hZF)) hZF source.omega source.transitive ht hm ha source.omega_mem
  have theory := source.theory.map_l _ hZF source.omega source.transitive ht hm ha hp
  obtain ⟨K', small⟩ := source.successor_l hZF hm ha ht hp (hp.1.1.output_mem_of_pairMember hw) (fun _ h => h)
    (sc_ordinal_small_l hZF source.omega ht ha theory (hp.1.1.output_mem_of_pairMember hw) (source.omega.isOrdinal hZF))
  exact ⟨z, R, S, V, a, K, K', K₀, hm, ha, hz, source, small, ambient, hA, rank, limit, hp⟩

/-- 实际原树步和已有前驱证书自动产生下一行及完整工作超幂。 -/
theorem Ic_row_d.step_l
    {ω c X A π z Z α b H B σ u U β κ L F o P Rₚ Kₚ j₀ : M.Domain}
    (row : Ic_row_d (ZFC.models_zf_l hZFC) ω c X A π z Z α)
    (own : Ic_row_d (ZFC.models_zf_l hZFC) ω b H B σ u U β)
    (hp : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) o P Rₚ)
    (sp : Ep_source_d (ZFC.models_zf_l hZFC) ω ω Kₚ P Rₚ)
    (loc : It_local_d ω H κ L F) (agree : Ea_agree_d ω κ X H)
    (strength : Ex_strength_d (ZFC.models_zf_l hZFC) ω κ L H F) (card : Sc_inaccessible_d ω H L)
    (prior : (X = H ∧ A = B ∧ π = σ) ∨ ∃ ρ φ, Pn_agree_d X A π H B σ ρ φ ∧ Es_strength_d X ρ H)
    (ultra : It_ultra_d (ZFC.models_zf_l hZFC) ω κ L F c o j₀) :
    ∃ κ' L' F' N n A' α' j k, Ic_row_d (ZFC.models_zf_l hZFC) ω o P A' k n N α' ∧
      Rd_entry_d κ κ' σ ∧ Rd_entry_d L L' σ ∧ Rd_entry_d F F' σ ∧ Rd_entry_d α α' j ∧ Rd_entry_d A A' j ∧
      It_ultra_d (ZFC.models_zf_l hZFC) ω κ' L' F' z n j ∧
      (∀ x x' y y', Rd_entry_d x x' π → Rd_entry_d x y j₀ → Rd_entry_d x' y' j → Rd_entry_d y y' k) ∧
      Es_strength_d H L P ∧ Pn_agree_d H B σ P A' k L L' ∧ Ea_agree_d ω κ' Z U ∧
      It_local_d ω U κ' L' F' ∧ Ex_strength_d (ZFC.models_zf_l hZFC) ω κ' L' U F' ∧ Sc_inaccessible_d ω U L' := by
  let hZF := ZFC.models_zf_l hZFC
  have row₀ := row
  have own₀ := own
  obtain ⟨R, S, V, a, _, _, _, hm, ha, hz, sx, sa, sz, hA, ra, hα, hπ⟩ := row
  obtain ⟨Q, T, W, d, _, _, _, ho, hb, hu, sh, sb, su, hB, rb, hβ, hσ⟩ := own
  have copy := loc
  obtain ⟨_, hκ, hL, hF, pre⟩ := copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have ord := (loc.ordinals_l (ZF.modelsKP hZF) sh.transitive).1
  have below := ord.transitive ω pre.1.2.2.1
  obtain ⟨κ', _, hκσ⟩ := hσ.1.1.2.2 κ hκ
  obtain ⟨L', _, hLσ⟩ := hσ.1.1.2.2 L hL
  obtain ⟨F', _, hFσ⟩ := hσ.1.1.2.2 F hF
  obtain ⟨K₀, oh⟩ := sh.rebase_l hZF hκ below (sc_ordinal_small_l hZF sh.omega sh.transitive ho sh.theory hκ ord)
  have reverse : Ea_subset_d ω κ H X := fun m D C hm hd hc => (agree m D C hm hd hc).mpr
  obtain ⟨K₁, ox⟩ := reverse.alphabet_l hZF oh sx ord
  have point : Rd_entry_d κ κ' π := by
    rcases prior with ⟨_, _, rfl⟩ | ⟨ρ, φ, same, exactness⟩
    · exact hκσ
    · have lt := ea_critical_bound_l hZF ox oh agree ord same.source_limit.1 exactness.2
      obtain ⟨V₀, hv, _, rv, _, points⟩ := same.source_rank
      exact (points κ κ' (rv.ordinal_subset_l hZF sx.transitive hv κ lt)).mpr hκσ
  obtain ⟨_, _, _, a₀, _, _, _, hm₀, ha₀, hz₀, source, small, ambient, _, _, _, hp₀⟩ := row₀.rebase_l hZF ord below point
  obtain ⟨rfl, rfl⟩ := smem_unique_l I hZF.1 ha₀ ha
  obtain ⟨_, rfl⟩ := smdl_unique_l I hm₀.1 hm.1
  obtain ⟨_, rfl⟩ := smdl_unique_l I hz₀.1 hz.1
  obtain ⟨_, _, _, d₀, _, _, _, ho₀, hb₀, hu₀, owner, cut, outer, _, _, _, _⟩ := own₀.rebase_l hZF ord below hκσ
  obtain ⟨rfl, rfl⟩ := smem_unique_l I hZF.1 hb₀ hb
  obtain ⟨_, rfl⟩ := smdl_unique_l I ho₀.1 ho.1
  obtain ⟨_, rfl⟩ := smdl_unique_l I hu₀.1 hu.1
  have compatibility : Ea_agree_d ω κ' A B ∧ Ea_maps_d ω κ X π σ := by
    rcases prior with ⟨_, rfl, rfl⟩ | ⟨ρ, φ, same, exactness⟩
    · exact ⟨fun _ _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ _ _ h => h⟩
    · have lt := ea_critical_bound_l hZF source owner agree ord same.source_limit.1 exactness.2
      have lt' := ((hb.2 κ' φ).mp ((hσ.relation_l I hZF sx.omega ho.1 hb.1 hκσ same.right_end).mp
        ((ho.2 κ ρ).mpr ⟨hκ, hσ.1.1.input_mem_of_pairMember same.right_end, lt⟩))).2.2
      exact (same.copy_l hZF source owner small cut lt lt').2
  have card' := (card.map_l hZF sx.omega owner.transitive cut.transitive ho hb hσ hLσ).of_rank_l hZF
    outer.source.transitive outer.source.theory.algebra.pair hB rb hβ
  obtain ⟨regular, sizes⟩ := outer.inaccessible L' card'
  have data := card'
  obtain ⟨_, _, pre'⟩ := data
  have above : M.mem ω L' := (Formula.satisfies_mem_iff _ _ _).mp ((Formula.satisfies_conj_iff _ _ _).mp pre').1
  obtain ⟨N, Rₙ, n, j, Kₙ, α', A', S', a', k, K', hn, big, next, hαα, hAA, hl, hA', ra', ha', small', hk,
    commute, exactness, adjacent, zu, up, strong, card''⟩ := ic_copy_step_l hZFC source owner small cut ambient outer.source
      (outer.closed.bounded_l outer.source.transitive) outer.power outer.cover (regular ω above) sizes hA ra hα hB rb hβ
      hm ho ha hb hz hπ hσ point hκσ hLσ hFσ agree compatibility.1 compatibility.2 loc strength card hp ultra
  obtain ⟨K₂, sn⟩ := next.rebase_l hZF next.source.omega_mem (fun _ h => h)
    (next.source.cardinal_small.mono_l next.source.below)
  obtain ⟨K₃, sc⟩ := small'.rebase_l hZF small'.omega_mem (fun _ h => h) (small'.cardinal_small.mono_l small'.below)
  exact ⟨κ', L', F', N, n, A', α', j, k,
    ⟨Rₚ, S', Rₙ, a', Kₚ, K₃, K₂, hp, ha', hn, sp, sc, sn, hA', ra', hl, hk⟩,
    hκσ, hLσ, hFσ, hαα, hAA, big, commute, exactness, adjacent, zu, up, strong, card''⟩

end YesMetaZFC.SetTheory.LargeCardinal
