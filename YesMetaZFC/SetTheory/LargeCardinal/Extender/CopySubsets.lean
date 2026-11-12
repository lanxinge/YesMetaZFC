import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.SetTheory.LargeCardinal.Extender.FunctionMap
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceTrace
import YesMetaZFC.SetTheory.LargeCardinal.Extender.ValueBound
import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraSupport
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySeed

/-! # 实际支撑迹沿所属源嵌入传输

测度关系、恒等代表与有界分离方程一同传输；完整有限列空间保证目标中
新出现的列也由同一方程判定，因此得到实际集合的像，而非仅逐点像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_trace_d.map_l {ω κ κ' L L' K K' X R Y S c d σ F F' m D D' E E' a a' f f' Z Z' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hσ : Smap_d I ω c d X Y σ)
    (theory : Sc_theory_d I ω Y S) (hωX : M.mem ω X) (hmω : M.mem m ω)
    (hκ : Rd_entry_d κ κ' σ) (hL : Rd_entry_d L L' σ) (hK : Rd_entry_d K K' σ)
    (hF : Rd_entry_d F F' σ) (hD : Rd_entry_d D D' σ) (hE : Rd_entry_d E E' σ)
    (ha : Rd_entry_d a a' σ) (hf : Rd_entry_d f f' σ) (hZ : Rd_entry_d Z Z' σ)
    (trace : Eb_trace_d ω κ L K X F m D E a f Z) : Eb_trace_d ω κ' L' K' Y F' m D' E' a' f' Z' := by
  obtain ⟨B, J, U, V, ι, T, hBX, hJX, hUX, hVX, hιX, hTX, kb, indices, range, rel, fb, fi, ids, seq, sub, spec⟩ := trace
  obtain ⟨B', hBY, hB⟩ := hσ.1.1.2.2 B hBX
  obtain ⟨J', hJY, hJ⟩ := hσ.1.1.2.2 J hJX
  obtain ⟨U', hUY, hU⟩ := hσ.1.1.2.2 U hUX
  obtain ⟨V', hVY, hV⟩ := hσ.1.1.2.2 V hVX
  obtain ⟨ι', hιY, hι⟩ := hσ.1.1.2.2 ι hιX
  obtain ⟨T', hTY, hT⟩ := hσ.1.1.2.2 T hTX
  have ωσ := hσ.omega_l I hZF hω hX hY hm hn hωX
  have mσ := hσ.natural_l hZF hω hX hY hm hn hωX m hmω
  have indices' := ep_indices_map_l hZF hω hX hY hm hn hσ theory hωX hL hJ indices
  have seq₀ : Fseq_space_d I ω L T := fun t => (seq t).trans (exists_congr fun n => and_congr_right fun _ =>
    ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩)
  have seq' := hσ.sequences_l hZF hω hX hY hm hn theory hωX hL hT seq₀
  let φ : Formula 1 17 := .conj (rd_graph_m .range (.bound 5) (.bound 5) (.bound 5) (.bound 7))
    (.conj (rd_graph_m .mem (.bound 10) (.bound 10) (.bound 10) (.bound 6))
      (.conj (fn0_m (.bound 15) (.bound 10) (.bound 2))
        (.conj (fn0_m (.bound 16) (.bound 16) (.bound 4))
          (.conj (Formula.forallMem (.bound 16) (rd_entry0_m .newest .newest (.bound 5)))
            (.conj (Formula.subset .newest (.bound 1)) (Formula.forallMem (.bound 1)
              (.iff (.mem .newest (.bound 1)) (.conj (fn0_m (.bound 15) (.bound 12) .newest)
                (eb_edge_m (.bound 14) (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9)
                  (.bound 8) (.bound 7) (.bound 6) .newest (.bound 5) (.bound 4) (.bound 3))))))))))
  have delta : φ.IsDelta0 := .conj (rd_graph_delta_l ..) (.conj (rd_graph_delta_l ..)
    (.conj (fn0_delta_l ..) (.conj (fn0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..))
      (.conj (.atom ..) (.forallMem _ (.iff (.mem ..) (.conj (fn0_delta_l ..) (eb_edge_delta_l ..)))))))))
  have tr := smap_delta_l I hZF hω hX hY hm hn hσ φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) delta
    ⟨Fin.cases Z (Fin.cases T (Fin.cases f (Fin.cases a (Fin.cases ι (Fin.cases F (Fin.cases V
      (Fin.cases U (Fin.cases K (Fin.cases J (Fin.cases B (Fin.cases L (Fin.cases κ (Fin.cases ω
        (Fin.cases m (Fin.cases D (fun _ => E)))))))))))))))), fun _ => E⟩
    ⟨Fin.cases Z' (Fin.cases T' (Fin.cases f' (Fin.cases a' (Fin.cases ι' (Fin.cases F' (Fin.cases V'
      (Fin.cases U' (Fin.cases K' (Fin.cases J' (Fin.cases B' (Fin.cases L' (Fin.cases κ' (Fin.cases ω
        (Fin.cases m (Fin.cases D' (fun _ => E')))))))))))))))), fun _ => E'⟩
    (Fin.cases hZ (Fin.cases hT (Fin.cases hf (Fin.cases ha (Fin.cases hι (Fin.cases hF (Fin.cases hV
      (Fin.cases hU (Fin.cases hK (Fin.cases hJ (Fin.cases hB (Fin.cases hL (Fin.cases hκ (Fin.cases ωσ
        (Fin.cases mσ (Fin.cases hD (fun _ => hE)))))))))))))))))
  simp only [φ, Formula.satisfies_conj_iff, rd_graph_sat_l (ZF.modelsKP hZF), fn0_sat_l hZF.1,
    Formula.satisfies_forallMem_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, eb_edge_sat_l hZF.1] at tr
  obtain ⟨range', rel', fb', fi', ids', sub', spec'⟩ := tr.mp ⟨range, rel, fb, fi, ids, sub, spec⟩
  exact ⟨B', J', U', V', ι', T', hBY, hJY, hUY, hVY, hιY, hTY,
    (hσ.subset_l hZF hω hX hY hm hn hK hB).mp kb, indices', range', rel', fb', fi', ids',
    (fun t => (seq' t).trans (exists_congr fun n => and_congr_right fun _ =>
      ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩)), sub', spec'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 复制图与所属嵌入在全部有限支撑幂子集上一致

常值 κ 的像界住整个支撑，从而每个子集都有有限 κ 幂子集值的代表。
两图在这种代表上一致；所属源计算的实际迹沿 σ 搬运，再在复制超幂中
读取。端点 k(L)=σ(L) 保证复制值恰好等于这个完整迹。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_copy_subsets_l
    {ω κ κ' K K' K₂ K₀ K₁ L L' X R Y S X' R' N R₀ N' R₁ c d b b' π σ F F'
      J O Z A p T V q c₀ C W J' O' Z' A' p' T' V' q' c₁ C' W' P Rₚ o P' Rₚ' o' B₁ R₁' b₁ g g' k : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y S)
    (ambient : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K₂ X' R') (inside : M.MemberSubset Y X')
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ N R₀) (owner' : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K₁ N' R₁)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁) (hσ : Smap_d I ω b b' N N' σ)
    (hκπ : Rd_entry_d κ κ' π) (hκσ : Rd_entry_d κ κ' σ) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (maps : Ea_maps_d ω κ X π σ)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (family' : Em_source_d ω κ' L' X' F') (coherent' : Ec_source_d I ω κ' L' X' F')
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c₀ C W) (hP : M.TransitiveSet P) (mdl : Smem_d I o P Rₚ)
    (hg : Smap_d I ω c₀ o C P g) (range : M.IsRangeOf I P g)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α g)
    (system' : Ep_system_d I ω κ' L' X' R' F' J' O' Z' A' p' T' V') (limit' : Di_limit_d A' p' T' V' q' C' W')
    (model' : Smdl_d I c₁ C' W') (hB : M.TransitiveSet B₁) (mb : Smem_d I b₁ B₁ R₁')
    (hg' : Smap_d I ω c₁ b₁ C' B₁ g') (fixed' : ∀ α H, Ep_seed_d κ' L' q' α H → Rd_entry_d H α g')
    (hP' : M.TransitiveSet P') (mdl' : Smem_d I o' P' Rₚ')
     (hk : Smap_d I ω o o' P P' k) (hLk : Rd_entry_d L L' k)
    (copied : ∀ a a' f f' x y, Rd_entry_d a a' σ → Rd_entry_d f f' π →
      Ep_value_d q g a f x → Ep_value_d q' g' a' f' y → Rd_entry_d x y k) :
    Ea_maps_d ω L P k σ := by
  have eq := hZF.1.eq_of_same_members K₀ K (fun f => ((owner.finite_l (ZF.modelsKP hZF)) f).trans ((source.finite_l (ZF.modelsKP hZF)) f).symm)
  subst K₀
  have eq := hZF.1.eq_of_same_members K₁ K' (fun f => ((owner'.finite_l (ZF.modelsKP hZF)) f).trans ((target.finite_l (ZF.modelsKP hZF)) f).symm)
  subst K₁
  have eq := hZF.1.eq_of_same_members K₂ K' (fun f => ((ambient.finite_l (ZF.modelsKP hZF)) f).trans ((target.finite_l (ZF.modelsKP hZF)) f).symm)
  subst K₂
  obtain ⟨K₂, _, hKK⟩ := hσ.1.1.2.2 K owner.finite.mem_l
  have finite := hσ.sequences_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ owner'.theory
    owner.omega_mem hκσ hKK (owner.finite_l (ZF.modelsKP hZF))
  have eq := hZF.1.eq_of_same_members K₂ K' (fun f => (finite f).trans ((target.finite_l (ZF.modelsKP hZF)) f).symm)
  subst K₂
  have hLN := hσ.1.1.input_mem_of_pairMember hLσ
  have hFN := hσ.1.1.input_mem_of_pairMember hFσ
  have hJN := ep_indices_mem_l hZF owner hLN system.indices
  intro m Q B B' hmω hQ hBP bound hBB
  obtain ⟨H, hHB⟩ := (range B).mp hBP
  obtain ⟨n, a, D, f, hnω, haJ, ha, hd, hfX, ff, fv⟩ :=
    ep_repr_surjective_l hZF family system limit (hg.1.1.input_mem_of_pairMember hHB)
  -- 在同一支撑上取常值界，保留原集合的同一超幂值。
  obtain ⟨b₀, j, code, hj, constants⟩ := ep_value_constants_l hZFC source family coherent system limit model hg haJ ha hd
  obtain ⟨Γ, _, hκΓ⟩ := hj.1.1.2.2 κ source.cardinal_mem
  obtain ⟨u, huX, hu, uc, uv⟩ := constants κ Γ hκΓ
  have cover := ep_value_support_l hZF source family system limit model mdl hg fixed haJ hnω ha hd huX hu uc uv
  obtain ⟨E, hEX, he⟩ := source.space_l hZF hmω
  obtain ⟨f₀, hf₀X, fn, fb, value⟩ := ep_value_bound_l hZFC source family coherent system limit model hP mdl hg
    haJ hnω hmω ha hd he hfX ff ⟨H, fv, hHB⟩ hu
    (fun s x hsx => by
      have eq := (fn0_function_l (ZF.modelsKP hZF) hu).1.2 s x κ hsx (uc s (hu.bound_l hsx).1)
      exact eq ▸ (fun _ hx => hx)) uv (fun t ht => ((hQ t).mp (bound t ht)).mono_target_l cover)
  obtain ⟨f', hfY, hff⟩ := hπ.1.1.2.2 f₀ hf₀X
  have hfσ := maps.set_function_l hZF source owner target.transitive owner'.transitive hm hn hπ h₀ h₁ hσ
    hκπ hκσ hnω hmω hd he hf₀X fn fb hff
  have hfN := hσ.1.1.input_mem_of_pairMember hfσ
  obtain ⟨D', _, hDD⟩ := hπ.1.1.2.2 D (source.space_mem_l hZF hnω hd)
  obtain ⟨E', _, hEE⟩ := hπ.1.1.2.2 E hEX
  have hDσ := maps n D D D' hnω hd (source.space_mem_l hZF hnω hd) (fun _ h => h) hDD
  have hEσ := maps m E E E' hmω he hEX (fun _ h => h) hEE
  have hd' := ep_space_map_l hZF source target hm hn hπ hκπ hnω hd hDD
  have he' := ep_space_map_l hZF source target hm hn hπ hκπ hmω he hEE
  obtain ⟨a', _, haa⟩ := hσ.1.1.2.2 a (owner.transitive J hJN a haJ)
  have ha' := (hσ.function_l hZF source.omega owner.transitive owner'.transitive h₀ h₁
    (hσ.natural_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ owner.omega_mem n hnω) hLσ haa).mp ha
  have haJ' := (system'.indices a').mpr (ec_support_image_l hZF source.omega owner.transitive owner'.transitive
    h₀ h₁ hσ owner.omega_mem hLσ haa ((system.indices a).mp haJ))
  have fn' := (hπ.sfun_l hZF source.omega source.transitive target.transitive hm hn hDD hff
    (source.function_l hZF hf₀X fn)).function_l target.transitive
  obtain ⟨H', hHC', fv'⟩ := ep_repr_exists_l hZF family' system' limit' haJ' ha' hd' (inside f' hfY) (fn'.mono_target_l inside)
  obtain ⟨B'', _, hHB'⟩ := hg'.1.1.2.2 H' hHC'
  obtain ⟨H₀, fv₀, hH₀B⟩ := value
  have mapped := copied a a' f₀ f' B B'' haa hff ⟨H₀, fv₀, hH₀B⟩ ⟨H', fv', hHB'⟩
  have eq := hk.1.1.1.2 B B'' B' mapped hBB
  subst B''
  -- 所属源内实际分离出的迹先辨认为 B，再沿 σ 搬运。
  have fnN := fn.retarget_l (fun s x hsx => (rd_entry_transitive_l owner.transitive hfN hsx).2)
  obtain ⟨B₀, hB₀, trace⟩ := eb_trace_l hZF owner hLN hFN system.indices haJ hmω he hfN fnN
  have read := trace.read_l hZFC source family coherent system limit model hP mdl hg fixed
    hnω hmω ha hd he hf₀X ⟨H₀, fv₀, hH₀B⟩
  have eq := hZF.1.eq_of_same_members B₀ B fun t => (read t).trans
    ⟨And.right, fun ht => ⟨(hQ t).mp (bound t ht), ht⟩⟩
  subst B₀
  obtain ⟨B₁, _, hBσ⟩ := hσ.1.1.2.2 B hB₀
  have trace' := trace.map_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ owner'.theory
    owner.omega_mem hmω hκσ hLσ hKK hFσ hDσ hEσ haa hfσ hBσ
  have read' := trace'.read_l hZFC ambient family' coherent' system' limit' model' hB mb hg' fixed'
    hnω hmω ha' hd' he' (inside f' hfY) ⟨H', fv', hHB'⟩
  have hωP := hj.1.1.output_mem_of_pairMember (hj.omega_l I hZF source.omega source.transitive hP code mdl source.omega_mem)
  have mσ := hk.natural_l hZF source.omega hP hP' mdl mdl' hωP m hmω
  have tr := smap_delta_l I hZF source.omega hP hP' mdl mdl' hk (n := 3)
    (ep_subspace_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (ep_subspace_delta_l ..)
    ⟨Fin.cases B (Fin.cases L (fun _ => m)), fun _ => m⟩
    ⟨Fin.cases B' (Fin.cases L' (fun _ => m)), fun _ => m⟩ (Fin.cases hBB (Fin.cases hLk (fun _ => mσ)))
  simp only [ep_subspace_sat_l hZF.1] at tr
  have bound' := tr.mp (fun t ht => (hQ t).mp (bound t ht))
  have eq := hZF.1.eq_of_same_members B₁ B' fun t => (read' t).trans
    ⟨And.right, fun ht => ⟨bound' t ht, ht⟩⟩
  exact eq ▸ hBσ

end YesMetaZFC.SetTheory.LargeCardinal
