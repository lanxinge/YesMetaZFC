import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRelationSyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSource
import YesMetaZFC.Model.SetTheory.Internal.SourcePower

/-! # 全部有界源代表组成的源内节点集

所有有限定义域都包含在同一个有限 κ 列空间中，因此一个相对幂集足以
容纳任意有限支撑的 B 值函数。节点只取这批原有函数，不增添外部代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Eb_pool_d (ω κ L X B J K P G A : M.Domain) : Prop where
  indices : M.mem J X
  powers : M.mem P X
  functions : M.mem G X
  carrier : M.mem A X
  subsets : FilterZF.Source_d X K P
  graphs : ∀ f, M.mem f G ↔ M.mem f X ∧
    ∀ p, M.mem p f → ∃ s, M.mem s K ∧ ∃ x, M.mem x B ∧ KPair_d M p s x
  nodes : ∀ u, M.mem u A ↔ Eb_node_d ω κ L K B J G P u

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_indices_mem_l {ω κ K X R L J : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (hL : M.mem L X) (indices : ∀ a, M.mem a J ↔ Ei_d ω L a) : M.mem J X := by
  obtain ⟨S, hS, seq⟩ := source.sequences.space L hL
  obtain ⟨c, code⟩ := source.code
  let ρ : Env M 2 := ⟨Fin.cases L (fun _ => ω), fun _ => L⟩
  let φ : UnarySchema 2 := { body := ei_m (.bound 2) (.bound 1) .newest }
  obtain ⟨J', hJ', spec⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory φ
    (ei_delta_l ..) ρ (Fin.cases hL (fun _ => source.omega_mem)) hS
  have eq : J' = J := hZF.1.eq_of_same_members J' J (fun a => by
    have read : φ.denote ρ a ↔ Ei_d ω L a := ei_sat_l hZF.1 ..
    rw [spec a, read, indices a]
    exact ⟨And.right, fun h => ⟨(seq a).mpr (h.elim fun n hn =>
      ⟨n, hn.1, fn0_function_l (ZF.modelsKP hZF) hn.2.1⟩), h⟩⟩)
  exact eq ▸ hJ'

theorem eb_pool_l {ω κ K X R L J B : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (power : Sc_power_d X) (hL : M.mem L X) (hB : M.mem B X)
    (indices : ∀ a, M.mem a J ↔ Ei_d ω L a) : ∃ P G A, Eb_pool_d ω κ L X B J K P G A := by
  obtain ⟨c, code⟩ := source.code
  have hJ := ep_indices_mem_l hZF source hL indices
  obtain ⟨P, hP, subsets⟩ := power K source.finite_mem
  obtain ⟨Q, hQ, product⟩ := source.theory.algebra.product K B source.finite_mem hB
  obtain ⟨G, hG, graphs⟩ := power Q hQ
  obtain ⟨V, hV, pair⟩ := source.theory.algebra.product J G hJ hG
  let ρ : Env M 8 := ⟨Fin.cases P (Fin.cases G (Fin.cases J (Fin.cases B
    (Fin.cases K (Fin.cases L (Fin.cases κ (fun _ => ω))))))), fun _ => ω⟩
  let φ : UnarySchema 8 := {
    body := eb_node_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨A, hA, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory φ (eb_node_delta_l ..) ρ
    (Fin.cases hP (Fin.cases hG (Fin.cases hJ (Fin.cases hB (Fin.cases source.finite_mem
      (Fin.cases hL (Fin.cases source.cardinal_mem (fun _ => source.omega_mem)))))))) hV
  refine ⟨P, G, A, hJ, hP, hG, hA, subsets, fun f => (graphs f).trans
    (and_congr_right fun _ => ⟨fun h p hp => (product p).mp (h p hp), fun h p hp => (product p).mpr (h p hp)⟩), fun u => ?_⟩
  exact (spec u).trans ((and_congr_right fun _ => eb_node_sat_l hZF.1 ..).trans
    ⟨And.right, fun h => ⟨h.elim (fun a ha => ha.2.elim (fun f hf => (pair u).mpr ⟨a, ha.1, f, hf.1, hf.2.1⟩)), h⟩⟩)

theorem Eb_pool_d.read_l {ω κ K X R L B J P G A u : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (pool : Eb_pool_d ω κ L X B J K P G A) (hu : M.mem u A) : ∃ n a D f,
      M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ M.mem f X ∧ Fn0_d D B f ∧ KPair_d M u a f := by
  obtain ⟨a, ha, f, hf, pair, n, hn, D, _, hna, space, fn⟩ := (pool.nodes u).mp hu
  exact ⟨n, a, D, f, hn, ha, hna, (eb_space_iff_l (ZF.modelsKP hZF) source.finite hn).mp space,
    ((pool.graphs f).mp hf).1, fn, pair⟩

theorem Eb_pool_d.node_l {ω κ K X R L B J P G A n a D f u : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (pool : Eb_pool_d ω κ L X B J K P G A) (hn : M.mem n ω) (ha : M.mem a J) (fn : Fn0_d n L a)
    (space : Ep_space_d κ n D) (hf : M.mem f X) (ff : Fn0_d D B f) (hu : KPair_d M u a f) : M.mem u A := by
  have dk s (hs : M.mem s D) : M.mem s K := (source.finite s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ((space s).mp hs)⟩
  exact (pool.nodes u).mpr ⟨a, ha, f, (pool.graphs f).mpr ⟨hf, fun p hp =>
    (ff.1 p hp).elim fun s hs => hs.2.elim fun x hx => ⟨s, dk s hs.1, x, hx⟩⟩, hu,
    n, hn, D, (pool.subsets D).mpr ⟨source.space_mem_l hZF hn space, dk⟩, fn,
      (eb_space_iff_l (ZF.modelsKP hZF) source.finite hn).mpr space, ff⟩

end YesMetaZFC.SetTheory.LargeCardinal
