import YesMetaZFC.SetTheory.LargeCardinal.IterationNice
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRelative

/-! # 原字母表所在秩层沿实际树根图固定

秩层本身作为共同对象保留；只要求根图逐点固定其成员。临界点可以移动
层号和整个秩层，因此这两个固定性命题严格分开。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_anchor_d (β B X π : M.Domain) : Prop where
  height : M.mem β X
  member : M.mem B X
  rank : Vr_d X β B
  fixed : ∀ x, M.mem x B → Rd_entry_d x x π

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际树中的恒等根图同时固定整个工作源及指定秩层。 -/
theorem It_diagram_d.anchor_root_l {ω α T J G i c X R β B : M.Domain}
    (tree : It_diagram_d hZF ω α T J G) (hc : Rd_entry_d i c J) (model : Smem_d I c X R)
    (ht : M.TransitiveSet X) (hβ : M.mem β X) (hB : M.mem B X) (rank : Vr_d X β B) :
    ∃ π, It_map_d G i i π ∧ (∀ x, M.mem x X → Rd_entry_d x x π) ∧ Tg_anchor_d β B X π := by
  obtain ⟨π, edge⟩ := tree.map_l hZF (tree.order.refl i ((tree.model_domain i).mpr ⟨c, hc⟩))
  have j := tree.elementary i i π c X R c X R edge hc hc model.1 model.1
  have fixed x (hx : M.mem x X) : Rd_entry_d x x π := by
    obtain ⟨y, _, image⟩ := j.1.1.2.2 x hx
    exact (tree.identity i π edge x y image).symm ▸ image
  exact ⟨π, edge, fixed, hβ, hB, rank, fun x hx => fixed x (ht B hB x hx)⟩

/-- 共用支撑秩层保存旧锚点，实际树的复合律保存根图的逐点固定性。 -/
theorem Tg_anchor_d.extend_l {ω β B X Y N π₀ π' κ L W V j α T J G o k i : M.Domain}
    (prior : Tg_anchor_d β B Y π₀) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y) (nt : M.TransitiveSet N)
    (hB : M.mem B X) (rankB : Vr_d X β B)
    (hW : M.mem W X) (rankW : Vr_d X L W) (hW' : M.mem W N) (rankW' : Vr_d N L W)
    (hL : M.IsLimitOrdinal L) (hκL : M.mem κ L) (below : M.MemberSubset β κ)
    (hV : M.mem V Y) (rankV : Vr_d Y κ V) (fixed : ∀ x, M.mem x V → Rd_entry_d x x j)
    (tree : It_diagram_d hZF ω α T J G) (root₀ : It_map_d G o k π₀)
    (edge : It_map_d G k i j) (root : It_map_d G o i π') : Tg_anchor_d β B N π' := by
  have hβL := ordinal_down_l (ZF.modelsKP hZF) (rankB.ordinal_l hB) hL.1 below hκL
  have hβW := rankW.ordinal_subset_l hZF xt hW β hβL
  obtain ⟨hBW, rankBW⟩ := rankW.rank_l hZF xt hW hL hβW hB rankB
  have sub := (rankV.compare_l hZF yt hV prior.member prior.rank below).1
  exact ⟨nt W hW' β hβW, nt W hW' B hBW, rankW'.of_rank_l hZF nt hW' hBW rankBW,
    fun x hx => tree.comp o k i π₀ j π' root₀ edge root x x x (prior.fixed x hx) (fixed x (sub x hx))⟩

/-- 完整初等图的真实临界点严格高于 ω。 -/
theorem Wd_crit_d.omega_lt_l {ω κ κ' X Y c R d S j : M.Domain}
    (critical : Wd_crit_d I X j κ κ') (hω : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (embed : Smap_d I ω c d X Y j) (hw : M.mem ω X) : M.mem ω κ := by
  have omega := embed.omega_l I hZF hω xt yt mx my hw
  have natural := embed.natural_l hZF hω xt yt mx my hw
  rcases (hω.isOrdinal hZF).trichotomy hZF.1 critical.ordinal (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) ω κ) with eq | lt | gt
  · have eq := hZF.1.eq_of_same_members ω κ eq
    exact (critical.moved (embed.1.1.1.2 κ κ κ' (eq ▸ omega) critical.image)).elim
  · exact lt
  · exact (critical.moved (embed.1.1.1.2 κ κ κ' (natural κ gt) critical.image)).elim

/-- 固定秩层中的整份有限原公式，沿同一根的两条实际图往返。 -/
theorem Tg_anchor_d.peer_l {ω β B r Z Q x X R y Y S π σ C₀ C D : M.Domain}
    (anchor : Tg_anchor_d β B X π) (target : Tg_anchor_d β B Y σ)
    (hω : M.IsOmega ω) (zt : M.TransitiveSet Z) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mz : Smem_d I r Z Q) (mx : Smem_d I x X R) (my : Smem_d I y Y S)
    (j : Smap_d I ω r x Z X π) (k : Smap_d I ω r y Z Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ) (ct : M.TransitiveSet C) (dt : M.TransitiveSet D)
    (nc : Nonempty {a // M.mem a C}) (nd : Nonempty {a // M.mem a D}) {n}
    (φ : Formula 1 n) (closed : φ.FreeClosed) (ρ : Env (rt_model_l C nc) n)
    (low : ∀ i, M.mem (ρ.bound i).val B) (valid : Formula.satisfies ρ φ) :
    ∃ θ : Env (rt_model_l D nd) n, (∀ i, (θ.bound i).val = (ρ.bound i).val) ∧ Formula.satisfies θ φ := by
  have fixed i := anchor.fixed (ρ.bound i).val (low i)
  have fixed' i := target.fixed (ρ.bound i).val (low i)
  have root i := (j.member_l I hZF hω mz mx (fixed i) iC).mpr (ρ.bound i).property
  have inside i := (k.member_l I hZF hω mz my (fixed' i) iD).mp (root i)
  have inhabited := nd
  obtain ⟨a⟩ := inhabited
  let θ : Env (rt_model_l D nd) n := ⟨fun i => ⟨(ρ.bound i).val, inside i⟩, fun _ => a⟩
  exact ⟨θ, fun _ => rfl, (smap_fixed_peer_l hZF hω zt xt yt mz mx my j k iC iD ct dt nc nd
    φ closed ρ θ (fun _ => rfl) fixed fixed').mp valid⟩

end YesMetaZFC.SetTheory.LargeCardinal
