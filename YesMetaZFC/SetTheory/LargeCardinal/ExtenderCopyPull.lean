import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTransport
import YesMetaZFC.Model.SetTheory.Internal.SourceTransport

/-! # 代表复制与有限坐标拉回交换

内部自然数和自然数之间的有限图逐点固定。拉回方程是纯语言中的三个
全称量词加有界矩阵；有限函数闭性保证目标中的每个新坐标列都被量化到。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_function_image_l {ω κ κ' K K' X R Y S c d π n f f' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω κ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (hκ : Rd_entry_d κ κ' π) (hnω : M.mem n ω) (hff : Rd_entry_d f f' π)
    (hf : Ep_fun_d κ X n f) : Ep_fun_d κ' Y n f' := by
  obtain ⟨D, hd, hf⟩ := hf
  have hDX := source.space_mem_l hZF hnω hd
  obtain ⟨D', _, hDD⟩ := hπ.1.1.2.2 D hDX
  exact ⟨D', ep_space_map_l hZF source target hm hn hπ hκ hnω hd hDD,
    (hπ.sfun_l hZF source.omega source.transitive target.transitive hm hn hDD hff
      (source.function_l hZF (hπ.1.1.input_mem_of_pairMember hff) hf)).function_l target.transitive⟩

theorem ep_pull_image_l {ω κ κ' K K' X R Y S c d π m n q f f' g g' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω κ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (hκ : Rd_entry_d κ κ' π) (hmω : M.mem m ω) (hnω : M.mem n ω) (hq : Fn0_d m n q)
    (hff : Rd_entry_d f f' π) (hgg : Rd_entry_d g g' π) (pull : Ep_pull_d κ X m n q f g) :
    Ep_pull_d κ' Y m n q f' g' := by
  have qω := hq.mono_target_l (source.omega.transitive hZF n hnω)
  have hqX := sc_finite_function_l hZF source.omega source.transitive hm source.theory
    source.omega_mem (source.transitive ω source.omega_mem) hmω qω
  have hqq := hπ.finite_fixed_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem hmω hqX qω
  have nat := hπ.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem
  let nz : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, target.omega_mem⟩⟩
  let φ : Formula 1 9 := .imp (fn0_m (.bound 7) (.bound 6) (.bound 2))
    (.imp (cp0_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 1))
      (.iff (rd_entry0_m (.bound 1) .newest (.bound 4)) (rd_entry0_m (.bound 2) .newest (.bound 3))))
  have delta : φ.IsDelta0 := .imp (fn0_delta_l ..) (.imp (cp0_delta_l ..) (.iff (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))
  have read Z (hZ : M.TransitiveSet Z) (hz : Nonempty {x // M.mem x Z}) (ρ : Env (rt_model_l Z hz) 9) :
      Formula.satisfies ρ φ ↔ (Fn0_d (ρ.bound 7).val (ρ.bound 6).val (ρ.bound 2).val →
        Cp0_d (ρ.bound 8).val (ρ.bound 7).val (ρ.bound 6).val (ρ.bound 5).val (ρ.bound 2).val (ρ.bound 1).val →
        (Rd_entry_d (ρ.bound 1).val (ρ.bound 0).val (ρ.bound 4).val ↔ Rd_entry_d (ρ.bound 2).val (ρ.bound 0).val (ρ.bound 3).val)) := by
    apply (rt_model_delta_l hZ hz delta ρ).trans
    simp only [φ, Formula.satisfies_imp_iff, fn0_sat_l hZF.1, cp0_sat_l hZF.1,
      Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1]; rfl
  let ρ : Env M 6 := ⟨Fin.cases g (Fin.cases f (Fin.cases q (Fin.cases κ (Fin.cases n (fun _ => m))))), fun _ => ω⟩
  let η : Env M 6 := ⟨Fin.cases g' (Fin.cases f' (Fin.cases q (Fin.cases κ' (Fin.cases n (fun _ => m))))), fun _ => ω⟩
  have params : ∀ i, Rd_entry_d (ρ.bound i) (η.bound i) π :=
    Fin.cases hgg (Fin.cases hff (Fin.cases hqq (Fin.cases hκ (Fin.cases (nat n hnω) (fun _ => nat m hmω)))))
  let ρ' : Env (rt_model_l X nz) 6 := ⟨fun i => ⟨ρ.bound i, hπ.1.1.input_mem_of_pairMember (params i)⟩, fun _ => ⟨ω, source.omega_mem⟩⟩
  let η' : Env (rt_model_l Y ny) 6 := ⟨fun i => ⟨η.bound i, hπ.1.1.output_mem_of_pairMember (params i)⟩, fun _ => ⟨ω, target.omega_mem⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF source.omega ⟨c, R, d, S, hm.empty_pred_l I hz, hn.empty_pred_l I hz, hπ⟩ nz ny
    (.forallE (.forallE (.forallE φ))) (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) ρ' η' params
  simp only [Formula.satisfies_forall_iff, read X source.transitive nz, read Y target.transitive ny] at tr
  have next := tr.mp (fun s r x hs hsr => (pull.2.2 s.val r.val hs hsr x.val).symm)
  refine ⟨ep_function_image_l hZF source target hm hn hπ hκ hmω hff pull.1,
    ep_function_image_l hZF source target hm hn hπ hκ hnω hgg pull.2.1, fun s r hs hsr x => ?_⟩
  have hsY := sc_finite_function_l hZF target.omega target.transitive hn target.theory target.omega_mem (target.transitive κ' target.cardinal_mem) hnω hs
  have hrY := sc_finite_function_l hZF target.omega target.transitive hn target.theory target.omega_mem (target.transitive κ' target.cardinal_mem) hmω hsr.1
  by_cases hx : M.mem x Y
  · exact (next ⟨s, hsY⟩ ⟨r, hrY⟩ ⟨x, hx⟩ hs hsr).symm
  · exact iff_of_false (fun h => hx (rd_entry_transitive_l target.transitive (hπ.1.1.output_mem_of_pairMember hgg) h).2)
      (fun h => hx (rd_entry_transitive_l target.transitive (hπ.1.1.output_mem_of_pairMember hff) h).2)

end YesMetaZFC.SetTheory.LargeCardinal
