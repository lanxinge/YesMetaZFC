import YesMetaZFC.SetTheory.LargeCardinal.ExtenderClosedLimit
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderValueApply
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSupportRank
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthReturn

/-! # nice 后继保持背景可数闭性

可数目标序列选择成原代表列。源的闭性回收函数列，所属源的有界闭性与内部正则界
把支撑列放入两侧共同秩段。最后在目标内逐项计算 j(f)(a)，回收原序列本身。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_ultra_d.closed_l {ω κ K X R K' Y R' L F c d N S j : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (closed : Sc_omega_closed_d ω X) (owner_closed : Sc_bounded_omega_closed_d ω Y)
    (hierarchy : Sc_hierarchy_d X) (power : Sc_power_d X) (op : Sc_power_d Y) (oc : Sc_cover_d Y)
    (bound : Sc_omega_bound_d ω Y L) (sizes : Sc_rank_size_d I Y L) (hL : M.IsLimitOrdinal L)
    (loc : It_local_d ω Y κ L F) (strength : Ex_strength_d hZF ω κ L Y F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d hZF ω κ L F c d j) :
    Sc_omega_closed_d ω N := by
  have hN := ultra.transitive_l hZF hn.1
  obtain ⟨X₀, R₀, N₀, S₀, J, O, Z, D, p, T, V, q, b, C, W, i, e,
    mx, nx, system, limit, model, wc, bij, he, _, constants, hj, comp⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨en, es⟩ := smdl_unique_l I nx.1 hn.1
  subst X₀ R₀ N₀ S₀
  obtain ⟨P, hP, subsets⟩ := op K' owner.finite_mem
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory owner.finite hP subsets)).transfer_l reverse
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF)).transfer_l hZF reverse
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive
  have local_copy := loc
  obtain ⟨_, _, hLY, _, pre⟩ := local_copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hωL := hL.1.transitive κ pre.1.2.2.2.2.1 ω pre.1.2.2.1
  have below := hL.1.transitive ω hωL
  have fixed := (ep_seed_collapse_l hZF source ord.1.transitive hL.1.transitive below family coherent
    (loc.atoms_l hZF (owner.read_source_l hZF)) ((loc.normal_l hZF (owner.read_source_l hZF)).transfer_l hZF owner source agree.subset_l)
    system limit wc (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)).2
  have hLN := ep_support_mem_l hZFC source family coherent system limit model hN hn he fixed ord.1 hL.1
  have hw := hj.omega_l I hZF source.omega source.transitive hN hm hn source.omega_mem
  obtain ⟨K₀, base⟩ := source.successor_l hZF hm hn hN hj (hj.1.1.output_mem_of_pairMember hw) (fun _ h => h)
    ((hj.small_l hZF source.omega source.transitive hN hm hn hw).mp (source.cardinal_small.mono_l source.below))
  obtain ⟨K₁, target⟩ := base.rebase_l hZF hLN below
    (sc_ordinal_small_l hZF source.omega hN hn base.theory hLN hL.1)
  have next : Ep_successor_d hZF ω κ L X R F N S :=
    ⟨J, O, Z, D, p, T, V, q, b, C, W, d, e, system, limit, model, hn, hN, wc, bij, he⟩
  obtain ⟨W₀, hWY, rank, level, _, _, _⟩ := loc.rank_agree_l hZFC source owner target agree
    owner_closed.branch_l op oc
    ((sc_hierarchy_iff_l hZF source.omega source.transitive hN hm hn hj).mp hierarchy)
    ((sc_power_iff_l hZF source.omega source.transitive hN hm hn hj).mp power) sizes hL next strength
  intro s fs
  -- DC 选择同一序列的源函数和有限支撑；全部选择均为对象模型中的实际图。
  let ρ : Env M 3 := ⟨Fin.cases s (Fin.cases e (fun _ => q)), fun _ => s⟩
  let φ : BinarySchema 3 := { body := .existsE (.existsE (.conj
    (rd_entry_m (.bound 3) (.bound 1) (.bound 4)) (ep_value_m (.bound 6) (.bound 5) .newest (.bound 2) (.bound 1)))) }
  have sat u f : φ.denote ρ u f ↔ ∃ x a, Rd_entry_d u x s ∧ Ep_value_d q e a f x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1, ep_value_sat_l hZF.1]; rfl
  obtain ⟨G, fg, gs⟩ := dc_uniformize_formula_l hZF φ ρ source.omega (ZFC.dc_l I hZFC source.omega) (X := X) (fun u hu => by
    obtain ⟨x, hx, hux⟩ := fs.2.1 u hu
    obtain ⟨E, hE, hEx⟩ := bij.2 x hx
    obtain ⟨_, a, _, f, _, _, _, _, hf, _, fv⟩ := ep_repr_surjective_l hZF family system limit hE
    exact ⟨f, hf, (sat u f).mpr ⟨x, a, hux, E, fv, hEx⟩⟩)
  let η := ρ.push G
  let ψ : BinarySchema 4 := { body := .existsE (.existsE (.conj
    (rd_entry_m (.bound 3) (.bound 1) (.bound 5)) (.conj (rd_entry_m (.bound 3) .newest (.bound 4))
      (ep_value_m (.bound 7) (.bound 6) (.bound 2) .newest (.bound 1))))) }
  have read u a : ψ.denote η u a ↔ ∃ x f, Rd_entry_d u x s ∧ Rd_entry_d u f G ∧ Ep_value_d q e a f x := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1, ep_value_sat_l hZF.1]; rfl
  obtain ⟨A, fa, rows⟩ := dc_uniformize_formula_l hZF ψ η source.omega (ZFC.dc_l I hZFC source.omega) (X := J) (fun u hu => by
    obtain ⟨f, _, huf⟩ := fg.2.1 u hu
    obtain ⟨x, a, hux, E, fv, hEx⟩ := (sat u f).mp (gs u f huf)
    exact ⟨a, fv.index_l hZF system limit, (read u a).mpr ⟨x, f, hux, huf, E, fv, hEx⟩⟩)
  obtain ⟨L₀, hL₀, seq⟩ := owner.sequences.space L hLY
  have fa' := fa.mono_target_l (fun a ha => (seq a).mpr (((system.indices a).mp ha).elim
    fun n h => ⟨n, h.1, fn0_function_l (ZF.modelsKP hZF) h.2.1⟩))
  have hA := owner_closed L₀ hL₀ A fa'
  have hAW := ec_support_rank_l hZF owner hLY hL hωL bound hWY rank hA seq fa'
  have hAN := hN W₀ level.member A hAW
  have faW := fa.retarget_l (fun u a hua => (rd_entry_transitive_l (rank.transitive_l hZF owner.transitive hWY) hAW hua).2)
  -- j(G) 的所有自然数位置仍是原函数列的逐项像。
  obtain ⟨_, B, hB, fgB⟩ := source.function_l hZF (closed G fg) fg
  obtain ⟨B', hB', hBB⟩ := hj.1.1.2.2 B hB
  obtain ⟨G', hG', hGG⟩ := hj.1.1.2.2 G (closed G fg)
  have fg' := (hj.function_l hZF source.omega source.transitive hN hm hn hw hBB hGG).mp fgB
  have natural := hj.natural_l hZF source.omega source.transitive hN hm hn source.omega_mem
  have evaluate u (hu : M.mem u ω) : ∃ a f x, Rd_entry_d u a A ∧ Rd_entry_d u f G' ∧
      Rd_entry_d u x s ∧ M.IsSetFunction I f ∧ Rd_entry_d a x f := by
    obtain ⟨a, _, hua⟩ := fa.2.1 u hu
    obtain ⟨x, f, hux, huf, value⟩ := (read u a).mp (rows u a hua)
    obtain ⟨f', _, hff⟩ := hj.1.1.2.2 f (fg.bound_l huf).2
    have huf' := (hj.entry_l hZF source.omega source.transitive hN hm hn (natural u hu) hff hGG).mp huf
    have ax := ep_value_apply_l hZFC source family coherent system limit model hN hn he fixed constants comp hff value
    obtain ⟨E, fv, _⟩ := value
    obtain ⟨hf, n, hnω, _, D₀, space, ff⟩ := fv.source_l hZF family system limit
    obtain ⟨_, B₀, hB₀, ffB⟩ := source.function_l hZF hf ff
    obtain ⟨D₁, _, hDD⟩ := hj.1.1.2.2 D₀ (source.space_mem_l hZF hnω space)
    obtain ⟨B₁, _, hB₁⟩ := hj.1.1.2.2 B₀ hB₀
    have ff' := (hj.function_l hZF source.omega source.transitive hN hm hn hDD hB₁ hff).mp ffB
    exact ⟨a, f', x, hua, huf', hux, (fn0_function_l (ZF.modelsKP hZF) ff').1, ax⟩
  obtain ⟨U, hU, union⟩ := target.theory.algebra.union B' hB'
  obtain ⟨H, hH, coords⟩ := target.theory.algebra.envelope_l hU
  have bounded a f x (hf : M.mem f B') (hax : Rd_entry_d a x f) : M.mem x H := by
    obtain ⟨p, pair, hp⟩ := hax
    exact (coords a x ⟨p, pair, (union p).mpr ⟨f, hf, hp⟩⟩).2
  let ε : Env M 4 := ⟨Fin.cases A (Fin.cases G' (Fin.cases W₀ (fun _ => B'))), fun _ => A⟩
  let χ : BinarySchema 4 := { body := Formula.existsMem (.bound 4) (Formula.existsMem (.bound 6)
    (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 4)) (.conj
      (rd_entry0_m (.bound 3) .newest (.bound 5)) (rd_entry0_m (.bound 1) (.bound 2) .newest)))) }
  have test u x : χ.denote ε u x ↔ ∃ a, M.mem a W₀ ∧ ∃ f, M.mem f B' ∧
      Rd_entry_d u a A ∧ Rd_entry_d u f G' ∧ Rd_entry_d a x f := by
    simp only [χ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨t, ht, ft, select⟩ := sc_uniform_source_l hZF source.omega hN hn target.theory χ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))
    ε (Fin.cases hAN (Fin.cases hG' (Fin.cases level.member (fun _ => hB')))) target.omega_mem hH (fun u hu => by
      obtain ⟨a, f, x, hua, huf, _, _, hax⟩ := evaluate u hu
      exact ⟨x, bounded a f x (fg'.bound_l huf).2 hax,
        (test u x).mpr ⟨a, (faW.bound_l hua).2, f, (fg'.bound_l huf).2, hua, huf, hax⟩⟩)
  have eq := (ft.mono_target_l (hN H hH)).ext_l hZF.1 fs (fun u hu => by
    obtain ⟨a, f, x, hua, huf, hux, ff, hax⟩ := evaluate u hu
    obtain ⟨y, _, huy⟩ := ft.2.1 u hu
    obtain ⟨a', _, f', _, hua', huf', hay⟩ := (test u y).mp (select u y huy)
    have ea := (fn0_function_l (ZF.modelsKP hZF) fa).1.2 u a' a hua' hua
    have ef := (fn0_function_l (ZF.modelsKP hZF) fg').1.2 u f' f huf' huf
    subst a' f'
    exact ⟨x, ff.2 a y x hay hax ▸ huy, hux⟩)
  exact eq ▸ ht

end YesMetaZFC.SetTheory.LargeCardinal
