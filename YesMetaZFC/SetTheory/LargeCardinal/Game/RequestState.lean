import YesMetaZFC.SetTheory.LargeCardinal.Game.Archive
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundParity
import YesMetaZFC.Model.SetTheory.Relations.RecordImage

/-! # 下一原请求与实际档案列的共同状态

请求以所属模型中的真实记录码保存，轮号由同一数字图解释。反射上下文、
严格历史界、γ下界及整份档案列一起保留；档案短前缀沿共同图对应当前历史，供两种后继直接读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Tg_request_state_d (Ω γ Bγ C₀ S₀ X R w η C A σ χ z k D r : M.Domain)
    (f : Tg_archive_frame_d M.Domain) (v : Fin 46 → M.Domain) : Prop where
  context : Tg_context_d I w X R η C
  record : Rf_record_d I X R tg_issued0_m C r
  values : Rf_tuple_d I X R v r
  omega : v 0 = w
  external_omega : M.IsOmega Ω
  numbers : Rr_layer_d I Ω X R w z
  finite : M.mem k Ω
  index : M.PairMember I k (v 19) z
  sequence : M.IsSequenceOfLength I D k
  links : Tg_archive_links_d I f D
  names : Tg_archive_names_d I S₀ D
  name : ∃ p, It_map_d f.G f.o f.n p ∧ M.PairMember I S₀ (v 7) p
  views : Tg_archive_views_d I Ω γ Bγ C₀ D X R A σ w C (v 4) (v 1) (v 2) (v 3) z (v 20)
  lower : It_lower_d I γ X R (v 24)
  below : M.PairMember I χ (v 24) R

/-- 原记录直接恢复请求和同一个外部索引；所属模型只需外延性。 -/
theorem Tg_request_state_d.read_l (hKP : M.Models KP)
    {Ω γ Bγ C₀ S₀ X R w η C A σ χ z k D r : M.Domain} {v : Fin 46 → M.Domain}
    {f : Tg_archive_frame_d M.Domain}
    (h : Tg_request_state_d I Ω γ Bγ C₀ S₀ X R w η C A σ χ z k D r f v)
    (ext : Extensional (smdl_structure_l I (R := R) ⟨w,h.context.omega_mem⟩)) :
    let N := smdl_structure_l I (R := R) ⟨w,h.context.omega_mem⟩
    let Cn : N.Domain := ⟨C,h.context.member⟩
    ∃ nc : Nonempty {x : N.Domain // N.mem x Cn}, ∃ ι : Env (rt_model_l Cn nc) 46,
      (∀ i, (ι.bound i).val.val = v i) ∧ Formula.satisfies ι tg_issued0_m ∧
      Tg_round_index_d I Ω z ⟨w,h.context.omega_mem⟩ ⟨w,h.context.omega_mem⟩ (ι.bound 19).val k := by
  intro N Cn
  have fs := h.context.finite_l ⟨w,h.context.omega_mem⟩ ext
  let nc : Nonempty {x : N.Domain // N.mem x Cn} := ⟨⟨⟨w,h.context.omega_mem⟩,fs.omega_mem⟩⟩
  obtain ⟨ι,eq,issued⟩ := h.record.values_l I ⟨w,h.context.omega_mem⟩ ext tg_issued0_m tg_issued0_closed_l
    Cn ⟨r,h.record.elim fun mem _ => mem 1⟩ fs.transitive nc h.values
  have point : M.PairMember I k (ι.bound 19).val.val z := (eq 19).symm ▸ h.index
  obtain ⟨l,index⟩ := tg_round_index_l I hKP h.external_omega ⟨w,h.context.omega_mem⟩ ext
    ⟨w,h.context.omega_mem⟩ (ι.bound 19).val h.numbers ((h.numbers.image _).mpr ⟨k,h.finite,point⟩)
  have equal := h.numbers.injection.2 l k (ι.bound 19).val.val index.point point
  exact ⟨nc,ι,eq,issued,equal ▸ index⟩

end YesMetaZFC.SetTheory.LargeCardinal
