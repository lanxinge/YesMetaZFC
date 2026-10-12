import YesMetaZFC.SetTheory.LargeCardinal.TypeGameQueryBase
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnchor
import YesMetaZFC.SetTheory.LargeCardinal.TypePoolRead
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRelative

/-! # 原节点查询沿固定秩层传递

先由有限闭性读取最小常量域，把全部五条查询放回同一较低秩层。
随后沿两条实际根图搬运整份原查询证书，不将局部全称语义当作绝对性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 12)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem tg_query_base_rank_l {κ K X R β B : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (hC : M.mem C X) (fs : Fs_read_d ω C) (hB : M.mem B X) (rank : Vr_d X β B) (limit : M.IsLimitOrdinal β)
    (hw : p 0 = ω) (low : ∀ i : Fin 7, M.mem (p (i.castAdd 5)) B)
    (valid : Formula.satisfies ρ tg_query_base0_m) : ∀ i, M.mem (p i) B := by
  simp only [tg_query_base0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at valid
  obtain ⟨⟨U, D, basis, pool, root, max, bound, height, node⟩, _⟩ := valid
  let ξ := (ρ.push U).push D
  have basis := (rt_model_delta_l fs.transitive nc
    (tq_basis_delta_l (.bound 2) (.bound 7) (.bound 8) (.bound 6) (.bound 1)) ξ).mp basis
  simp only [tq_basis_sat_l hZF.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val] at basis
  obtain ⟨N, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ξ (.bound 2) (.bound 5) (.bound 1) (.bound 0) hw).mp pool
  have hwB : M.mem ω B := hw ▸ low 0
  obtain ⟨c, H, model⟩ := smdl_membership_l I hZF ⟨ω, hwB⟩
  have theory := source.rank_theory_l hZF hB rank limit model
  obtain ⟨S, hS, pair⟩ := theory.algebra.pair (p 0) (p 5) (low 0) (low 5)
  obtain ⟨T, hT, pair'⟩ := theory.algebra.pair (p 6) (p 4) (low 6) (low 4)
  obtain ⟨V, hV, sv, tv⟩ := rank.joint_bound_l source.transitive hB hS hT
  have hU : M.mem U.val B := rank.subset_mem_l source.transitive hB hV
    (source.transitive C hC U.val U.property) (fun x hx => by
      rcases (basis x).mp hx with eq | eq | eq | eq
      exact eq.symm ▸ sv _ ((pair _).mpr (Or.inl rfl))
      exact eq.symm ▸ sv _ ((pair _).mpr (Or.inr rfl))
      exact eq.symm ▸ tv _ ((pair' _).mpr (Or.inl rfl))
      exact eq.symm ▸ tv _ ((pair' _).mpr (Or.inr rfl)))
  have hD := (source.pool_rank_l hZF hB rank limit hwB (low 3) hU ⟨N, E, names, seq, product⟩).1
  have trans := rank.transitive_l hZF source.transitive hB D.val hD
  have hr : M.mem (p 7) D.val := ((Formula.satisfies_conj_iff ..).mp root).1
  have hm : M.mem (p 8) D.val := ((Formula.satisfies_conj_iff ..).mp max).1
  have hb : M.mem (p 9) D.val := ((Formula.satisfies_conj_iff ..).mp bound).1
  have hh : M.mem (p 10) D.val := ((Formula.satisfies_conj_iff ..).mp height).1
  have hq : M.mem (p 11) D.val := ((Formula.satisfies_conj_iff ..).mp node).1
  intro i
  exact Fin.cases (low 0) (Fin.cases (low 1) (Fin.cases (low 2) (Fin.cases (low 3) (Fin.cases (low 4)
    (Fin.cases (low 5) (Fin.cases (low 6) (Fin.cases (trans _ hr) (Fin.cases (trans _ hm)
      (Fin.cases (trans _ hb) (Fin.cases (trans _ hh) (Fin.cases (trans _ hq) (fun j => Fin.elim0 j)))))))))))) i

theorem Tg_anchor_d.query_peer_l {r Z Q x X R y Y S π σ C₀ D κ K β B : M.Domain}
    (anchor : Tg_anchor_d β B X π) (target : Tg_anchor_d β B Y σ)
    (nd : Nonempty {a // M.mem a D})
    (source : Ep_source_d hZF ω κ K X R) (hC : M.mem C X) (fs : Fs_read_d ω C)
    (zt : M.TransitiveSet Z) (yt : M.TransitiveSet Y) (dt : M.TransitiveSet D)
    (mz : Smem_d I r Z Q) (mx : Smem_d I x X R) (my : Smem_d I y Y S)
    (j : Smap_d I ω r x Z X π) (k : Smap_d I ω r y Z Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ) (limit : M.IsLimitOrdinal β)
    (hw : p 0 = ω) (low : ∀ i : Fin 7, M.mem (p (i.castAdd 5)) B)
    (valid : Formula.satisfies ρ tg_query_row0_m) :
    (∀ i, M.mem (p i) B) ∧ ∃ θ : Env (rt_model_l D nd) 12,
      (∀ i, (θ.bound i).val = p i) ∧ Formula.satisfies θ tg_query_row0_m := by
  have all := tg_query_base_rank_l hZF nc ρ source hC fs anchor.member anchor.rank limit hw low ((Formula.satisfies_conj_iff ..).mp valid).1
  exact ⟨all, anchor.peer_l hZF target source.omega zt source.transitive yt mz mx my j k iC iD fs.transitive dt
    nc nd tg_query_row0_m tg_query_row0_closed_l ρ all valid⟩

/-- 较早回答的三个查询只受 ω 和有限元数的共同秩界控制。 -/
theorem tg_reply_base_rank_l {κ K X R β B : M.Domain} (η : Env (rt_model_l C nc) 7)
    (source : Ep_source_d hZF ω κ K X R) (hC : M.mem C X) (fs : Fs_read_d ω C)
    (hB : M.mem B X) (rank : Vr_d X β B) (limit : M.IsLimitOrdinal β)
    (hw : (η.bound 0).val = ω) (low : ∀ i : Fin 4, M.mem (η.bound (i.castAdd 3)).val B)
    (valid : Formula.satisfies η tg_reply_base0_m) : ∀ i, M.mem (η.bound i).val B := by
  simp only [tg_reply_base0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at valid
  obtain ⟨U, D, pair, pool, root, bound, height⟩ := valid
  let ξ := (η.push U).push D
  have pair := (rt_model_delta_l fs.transitive nc (pair0_delta_l (.bound 1) (.bound 2) (.bound 2)) ξ).mp pair
  simp only [pair0_sat_l hZF.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val] at pair
  have hU := rank.pair_mem_l hZF source.transitive hB limit (low 0) (low 0)
    (source.transitive C hC U.val U.property) pair
  obtain ⟨N, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ξ (.bound 2) (.bound 5) (.bound 1) (.bound 0) hw).mp pool
  have hD := (source.pool_rank_l hZF hB rank limit (hw ▸ low 0) (low 3) hU ⟨N, E, names, seq, product⟩).1
  have trans := rank.transitive_l hZF source.transitive hB D.val hD
  have hr : M.mem (η.bound 4).val D.val := ((Formula.satisfies_conj_iff ..).mp root).1
  have hb : M.mem (η.bound 5).val D.val := ((Formula.satisfies_conj_iff ..).mp bound).1
  have hh : M.mem (η.bound 6).val D.val := ((Formula.satisfies_conj_iff ..).mp height).1
  intro i
  exact Fin.cases (low 0) (Fin.cases (low 1) (Fin.cases (low 2) (Fin.cases (low 3)
    (Fin.cases (trans _ hr) (Fin.cases (trans _ hb) (Fin.cases (trans _ hh) (fun j => Fin.elim0 j))))))) i

theorem Tg_anchor_d.reply_peer_l {r Z Q x X R y Y S π σ C₀ D κ K β B : M.Domain}
    (η : Env (rt_model_l C nc) 7) (anchor : Tg_anchor_d β B X π) (target : Tg_anchor_d β B Y σ)
    (nd : Nonempty {a // M.mem a D}) (source : Ep_source_d hZF ω κ K X R) (hC : M.mem C X) (fs : Fs_read_d ω C)
    (zt : M.TransitiveSet Z) (yt : M.TransitiveSet Y) (dt : M.TransitiveSet D)
    (mz : Smem_d I r Z Q) (mx : Smem_d I x X R) (my : Smem_d I y Y S)
    (j : Smap_d I ω r x Z X π) (k : Smap_d I ω r y Z Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ) (limit : M.IsLimitOrdinal β)
    (hw : (η.bound 0).val = ω) (low : ∀ i : Fin 4, M.mem (η.bound (i.castAdd 3)).val B)
    (valid : Formula.satisfies η tg_reply_base0_m) :
    (∀ i, M.mem (η.bound i).val B) ∧ ∃ θ : Env (rt_model_l D nd) 7,
      (∀ i, (θ.bound i).val = (η.bound i).val) ∧ Formula.satisfies θ tg_reply_base0_m := by
  have all := tg_reply_base_rank_l hZF nc η source hC fs anchor.member anchor.rank limit hw low valid
  exact ⟨all, anchor.peer_l hZF target source.omega zt source.transitive yt mz mx my j k iC iD fs.transitive dt
    nc nd tg_reply_base0_m tg_reply_base0_closed_l η all valid⟩

end YesMetaZFC.SetTheory.LargeCardinal
