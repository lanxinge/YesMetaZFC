import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRelative
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFinite

/-! # 复制时的有限幂、坐标与测度成员对应 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 全部有限单射支撑的集合沿初等嵌入传输，包含目标中的新支撑。 -/
theorem ep_indices_map_l {ω X R Y S c d σ L L' J J' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hσ : Smap_d I ω c d X Y σ)
    (theory : Sc_theory_d I ω Y S) (hωX : M.mem ω X)
    (hL : Rd_entry_d L L' σ) (hJ : Rd_entry_d J J' σ) (indices : ∀ a, M.mem a J ↔ Ei_d ω L a) :
    ∀ a, M.mem a J' ↔ Ei_d ω L' a := by
  have ωσ := hσ.omega_l I hZF hω hX hY hm hn hωX
  let φ : Formula 1 4 := .iff (.mem .newest (.bound 1)) (ei_m (.bound 3) (.bound 2) .newest)
  have tr := hσ.forall_delta_l hZF hω hX hY hm hn φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) (.iff (.mem ..) (ei_delta_l ..))
    ⟨Fin.cases J (Fin.cases L (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases J' (Fin.cases L' (fun _ => ω)), fun _ => ω⟩ (Fin.cases hJ (Fin.cases hL (fun _ => ωσ)))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, ei_sat_l hZF.1] at tr
  have read := tr.mp (fun a _ => indices a)
  exact fun a => ⟨fun ha => (read a (hY J' (hσ.1.1.output_mem_of_pairMember hJ) a ha)).mp ha, fun ha => by
    obtain ⟨n, hnω, fn, inj⟩ := ha
    have owned := sc_finite_function_l hZF hω hY hn theory (hσ.1.1.output_mem_of_pairMember ωσ)
      (hY L' (hσ.1.1.output_mem_of_pairMember hL)) hnω fn
    exact (read a owned).mpr ⟨n, hnω, fn, inj⟩⟩

theorem ep_space_map_l {ω μ μ' κ κ' K K' X R Y S c d π n D D' : M.Domain}
    (source : Ep_source_d hZF ω μ K X R) (target : Ep_source_d hZF ω μ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (hκ : M.PairMember I κ κ' π) (hnω : M.mem n ω) (space : Ep_space_d κ n D)
    (hD : M.PairMember I D D' π) : Ep_space_d κ' n D' := by
  have fixed := hπ.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem n hnω
  let φ : Formula 1 4 := .iff (.mem .newest (.bound 1)) (fn0_m (.bound 3) (.bound 2) .newest)
  have tr := hπ.forall_delta_l hZF source.omega source.transitive target.transitive hm hn φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) (.iff (.mem _ _) (fn0_delta_l ..))
    ⟨Fin.cases D (Fin.cases κ (fun _ => n)), fun _ => n⟩
    ⟨Fin.cases D' (Fin.cases κ' (fun _ => n)), fun _ => n⟩ (Fin.cases hD (Fin.cases hκ (fun _ => fixed)))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fn0_sat_l hZF.1] at tr
  have read := tr.mp (fun f _ => space f)
  intro f
  exact ⟨fun hf => (read f (target.transitive D' (hπ.1.1.output_mem_of_pairMember hD) f hf)).mp hf,
    fun hf => (read f (sc_finite_function_l hZF target.omega target.transitive hn target.theory target.omega_mem
      (target.transitive κ' (hπ.1.1.output_mem_of_pairMember hκ)) hnω hf)).mpr hf⟩

theorem ec_measure_image_l {ω c d N R N' S σ F F' a a' U V A A' : M.Domain}
    (hω : M.IsOmega ω) (hN : M.TransitiveSet N) (hN' : M.TransitiveSet N')
    (hm : Smem_d I c N R) (hn : Smem_d I d N' S) (hσ : Smap_d I ω c d N N' σ)
    (hF : M.PairMember I F F' σ) (ha : M.PairMember I a a' σ) (hA : M.PairMember I A A' σ)
    (hU : Rd_entry_d a U F) (hV : Rd_entry_d a' V F')
    (unique : ∀ x y z, Rd_entry_d x y F' → Rd_entry_d x z F' → y = z) : M.mem A U ↔ M.mem A' V := by
  obtain ⟨U', _, hUU⟩ := hσ.1.1.2.2 U (rd_entry_transitive_l hN (hσ.1.1.input_mem_of_pairMember hF) hU).2
  have entry := (hσ.entry_l hZF hω hN hN' hm hn ha hUU hF).mp hU
  have eq := unique a' U' V entry hV
  have tr := smap_delta_l I hZF hω hN hN' hm hn hσ (n := 2) (.mem (.bound 1) .newest)
    (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.mem _ _)
    ⟨Fin.cases U (fun _ => A), fun _ => A⟩ ⟨Fin.cases U' (fun _ => A'), fun _ => A'⟩ (Fin.cases hUU (fun _ => hA))
  simp only [Formula.satisfies_mem_iff] at tr
  exact eq ▸ tr

theorem ec_support_image_l {ω c d N R N' S σ L L' a a' : M.Domain}
    (hω : M.IsOmega ω) (hN : M.TransitiveSet N) (hN' : M.TransitiveSet N')
    (hm : Smem_d I c N R) (hn : Smem_d I d N' S) (hσ : Smap_d I ω c d N N' σ)
    (hωN : M.mem ω N) (hL : M.PairMember I L L' σ) (haa : M.PairMember I a a' σ)
    (ha : Ei_d ω L a) : Ei_d ω L' a' := by
  obtain ⟨n, hnω, ha, inj⟩ := ha
  have image := hσ.finite_injection_l hZF hω hN hN' hm hn hωN hnω hL haa
    ⟨fn0_function_l (ZF.modelsKP hZF) ha, inj⟩
  exact ⟨n, hnω, fn0_of_function_l (ZF.modelsKP hZF) image.1, image.2⟩

theorem ec_index_image_l {ω c d N R N' S σ L L' a a' b b' q m n : M.Domain}
    (hω : M.IsOmega ω) (hN : M.TransitiveSet N) (hN' : M.TransitiveSet N')
    (hm : Smem_d I c N R) (hn : Smem_d I d N' S) (hσ : Smap_d I ω c d N N' σ)
    (theory : Sc_theory_d I ω N R) (hωN : M.mem ω N) (hL : Rd_entry_d L L' σ)
    (haa : Rd_entry_d a a' σ) (hbb : Rd_entry_d b b' σ)
    (hmω : M.mem m ω) (hnω : M.mem n ω) (hq : Fn0_d m n q) (hb : Fn0_d n L b) (ha : Cp0_d m n L q b a) :
    Fn0_d n L' b' ∧ Cp0_d m n L' q b' a' := by
  have qω := hq.mono_target_l (hω.transitive hZF n hnω)
  have hqN := sc_finite_function_l hZF hω hN hm theory hωN (hN ω hωN) hmω qω
  have hqq := hσ.finite_fixed_l hZF hω hN hN' hm hn hωN hmω hqN qω
  have nat := hσ.natural_l hZF hω hN hN' hm hn hωN
  exact ⟨(hσ.function_l hZF hω hN hN' hm hn (nat n hnω) hL hbb).mp hb,
    (hσ.composition_l hZF hω hN hN' hm hn (nat m hmω) (nat n hnω) hL hqq hbb haa).mp ha⟩

end YesMetaZFC.SetTheory.LargeCardinal
