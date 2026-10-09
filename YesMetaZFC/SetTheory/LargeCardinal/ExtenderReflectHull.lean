import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadSource
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankSource
import YesMetaZFC.Model.SetTheory.Internal.ElementaryHull
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOrdinal
import YesMetaZFC.SetTheory.Collapse.EmbeddingFixed
import YesMetaZFC.Model.SetTheory.LevyReflection
import YesMetaZFC.SetTheory.CumulativeRegularCover
import YesMetaZFC.SetTheory.Card.FiniteParameters
import YesMetaZFC.SetTheory.Card.CountablePair

/-! # 有限反射层的实际可数壳

先反射到极限秩层，再在拥有它的正则秩层中取壳。外层提供完整源证书，
内层原像提供读取有限代表所需的闭性；不要求反射高度正则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_reflect_hull_l {ω : M.Domain} (hω : M.IsOmega ω) {n m}
    (v : Fin n → M.Domain) (φ : Formula 1 m) (hφ : φ.FreeClosed) :
    ∃ B R b K U S u J C V π,
      Ep_source_d hZF ω ω K B R ∧ Ep_source_d hZF ω ω J U S ∧ Smem_d I b B R ∧ Smem_d I u U S ∧
      Smap_d I ω b u B U π ∧ M.CardinalLessOrEqual I B ω ∧ M.mem C B ∧ Fs_read_d ω C ∧ M.TransitiveSet V ∧
      Rd_entry_d C V π ∧ Lr_reflect_d φ V ∧ ∀ i, ∃ x, M.mem x C ∧ Rd_entry_d x (v i) π := by
  obtain ⟨A, _, aset⟩ := ZF.finite_params_l I hZF hω (Fin.cases ω v)
  obtain ⟨θ, V, rank, limit, hA, reflect⟩ := ZF.lr_reflect_l I hZF φ hφ A
  have vt := ZF.v_transitive_l I hZF rank
  have hωV := vt A hA ω ((aset ω).mpr ⟨0, rfl⟩)
  have hv i : M.mem (v i) V := vt A hA (v i) ((aset (v i)).mpr ⟨i.succ, rfl⟩)
  let w : Fin (n + 3) → M.Domain := Fin.cases ω (Fin.cases V (Fin.cases θ v))
  obtain ⟨P, finite, pset⟩ := ZF.finite_params_l I hZF hω w
  obtain ⟨δ, U, regular, above, outer, hP⟩ := ZFC.v_regular_cover_l I hZFC hω P
  have ut := ZF.v_transitive_l I hZF outer
  have owned i : M.mem (w i) U := ut P hP (w i) ((pset (w i)).mpr ⟨i, rfl⟩)
  obtain ⟨J, seq⟩ := ZF.fseq_space_exists_l I hZF hω ω
  obtain ⟨S, target⟩ := ep_regular_source_l hZFC hω above regular outer above (fun _ h => h) seq
  obtain ⟨u, mu⟩ := target.code
  obtain ⟨A₀, seed⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω P
  obtain ⟨id, identity⟩ := ZF.exists_identityBijection hZF I ω
  have small := ZF.countable_union_two_l I hZF hω ⟨id, identity.1⟩
    (ZF.finite_countable_l I hZF hω finite) seed
  have inside x (hx : M.mem x A₀) : M.mem x U :=
    ((seed x).mp hx).elim (ut ω (owned 0) x) (ut P hP x)
  obtain ⟨X, d, T, B, F, π, b, R, _, cover, _, _, bt, collapse, count, inverse, mb, hj⟩ :=
    selem_hull_collapse_l hZFC hω ut mu inside small
  have preimage x (hx : M.mem x A₀) : ∃ y, Rd_entry_d y x π := by
    obtain ⟨y, _, hy⟩ := collapse.1.2.1 x (cover x hx)
    exact ⟨y, (inverse x y).mpr hy⟩
  have param i : ∃ x, Rd_entry_d x (w i) π :=
    preimage (w i) ((seed (w i)).mpr (Or.inr ((pset (w i)).mpr ⟨i, rfl⟩)))
  have rel x y a c (hx : Rd_entry_d x a π) (hy : Rd_entry_d y c π) := hj.member_l I hZF hω mb mu hx hy
  obtain ⟨W, ws⟩ := KP.exists_insert (ZF.modelsKP hZF) ω ω
  have wt : M.TransitiveSet W := by
    intro x hx y hy
    apply (ws y).mpr
    exact Or.inl (((ws x).mp hx).elim (fun hx => hω.transitive hZF x hx y hy) (fun e => e ▸ hy))
  obtain ⟨wb, fixed⟩ := mem_embedding_fixed_l hZF bt hj.1 rel wt (fun x hx => by
    rcases (ws x).mp hx with hx | rfl
    · exact preimage x ((seed x).mpr (Or.inl hx))
    · exact param 0)
  have hωW := (ws ω).mpr (Or.inr rfl)
  have hωB := wb ω hωW
  have hωπ := fixed ω hωW
  obtain ⟨K, source⟩ := target.pull_l hZF bt hωB mb mu hj hωB (hω.isOrdinal hZF) (fun _ h => h)
  obtain ⟨C, hCV⟩ := param 1
  obtain ⟨α, hαθ⟩ := param 2
  have hC := hj.1.1.input_mem_of_pairMember hCV
  have hωC := (rel ω C ω V hωπ hCV).mpr hωV
  obtain ⟨D, H, hD, hH, certificate, _⟩ := vr_source_l hZF outer regular.isLimitOrdinal
    (ZF.v_ordinal_height_l hZF outer limit.1 (owned 2)) rank
  have rc := (hj.hierarchy_l hZF hω bt ut mb mu hαθ hCV).mpr ⟨D, H, hD, hH, fun t _ => certificate t⟩
  have lc := (hj.limit_l hZF hω bt ut mb mu hαθ).mpr limit
  refine ⟨B, R, b, K, U, S, u, J, C, V, π, source, target, mb, mu, hj, count, hC,
    source.rank_read_source_l hZF hC rc lc hωC, vt, hCV, reflect, fun i => ?_⟩
  obtain ⟨x, hx⟩ := param i.succ.succ.succ
  exact ⟨x, (rel x C (v i) V hx hCV).mpr (hv i), hx⟩

end YesMetaZFC.SetTheory.LargeCardinal
