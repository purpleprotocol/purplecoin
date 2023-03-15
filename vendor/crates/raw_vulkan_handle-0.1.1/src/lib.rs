#![no_std]

//! Rust definitions of the Vulkan "handle" and "non-dispatchable handle" types.
//!
//! The purpose of this crate is to be a small and stable public interface crate
//! so that other crates that both use Vulkan can pass handles between each
//! other when necessary without either directly depending on each other.

/// Makes a (dispatchable) handle.
macro_rules! define_handle {
  (
    $(#[$name_meta:meta])*
    $name:ident
  ) => {
    $(#[$name_meta])*
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    pub struct $name(*mut core::ffi::c_void);
    unsafe impl Send for $name {}
    unsafe impl Sync for $name {}
    impl $name {
      pub const NULL: Self = Self::null();
      #[inline]
      #[must_use]
      pub const fn null() -> Self {
        Self(core::ptr::null_mut())
      }
    }
    impl Default for $name {
      #[inline]
      #[must_use]
      fn default() -> Self {
        Self::NULL
      }
    }
  };
}

/// Makes a non-dispatchable handle.
macro_rules! define_non_dispatchable_handle {
  (
    $(#[$name_meta:meta])*
    $name:ident
  ) => {
    $(#[$name_meta])*
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    pub struct $name(
      #[cfg(target_pointer_width = "64")] *mut core::ffi::c_void,
      #[cfg(not(target_pointer_width = "64"))] u64,
    );
    unsafe impl Send for $name {}
    unsafe impl Sync for $name {}
    impl $name {
      pub const NULL: Self = Self(
        #[cfg(target_pointer_width = "64")]
        core::ptr::null_mut(),
        #[cfg(not(target_pointer_width = "64"))]
        0,
      );
      #[inline]
      #[must_use]
      pub const fn null() -> Self {
        Self::NULL
      }
    }
    impl Default for $name {
      #[inline]
      #[must_use]
      fn default() -> Self {
        Self::NULL
      }
    }
  };
}

//
// HANDLES
//

define_handle!(
  /// Khronos: [VkCommandBuffer](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkCommandBuffer.html) (handle)
  /// * Parent: [VkCommandPool]
  /// * Object Type Enum: `VK_OBJECT_TYPE_COMMAND_BUFFER`
  VkCommandBuffer
);
define_handle!(
  /// Khronos: [VkDevice](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDevice.html) (handle)
  /// * Parent: [VkPhysicalDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DEVICE`
  VkDevice
);
define_handle!(
  /// Khronos: [VkInstance](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkInstance.html) (handle)
  /// * Parent: none.
  /// * Object Type Enum: `VK_OBJECT_TYPE_INSTANCE`
  VkInstance
);
define_handle!(
  /// Khronos: [VkPhysicalDevice](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkPhysicalDevice.html) (handle)
  /// * Parent: [VkInstance]
  /// * Object Type Enum: `VK_OBJECT_TYPE_PHYSICAL_DEVICE`
  VkPhysicalDevice
);
define_handle!(
  /// Khronos: [VkQueue](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkQueue.html) (handle)
  /// * Parent: [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_QUEUE`
  VkQueue
);

//
// NON_DISPATCHABLE HANDLE
//

define_non_dispatchable_handle!(
  /// Khronos: [VkDeviceMemory](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDeviceMemory.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DEVICE_MEMORY`
  VkDeviceMemory
);
define_non_dispatchable_handle!(
  /// Khronos: [VkCommandPool](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkCommandPool.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_COMMAND_POOL`
  VkCommandPool
);
define_non_dispatchable_handle!(
  /// Khronos: [VkBuffer](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkBuffer.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_BUFFER`
  VkBuffer
);
define_non_dispatchable_handle!(
  /// Khronos: [VkBufferView](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkBufferView.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_BUFFER_VIEW`
  VkBufferView
);
define_non_dispatchable_handle!(
  /// Khronos: [VkImage](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkImage.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_IMAGE`
  VkImage
);
define_non_dispatchable_handle!(
  /// Khronos: [VkImageView](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkImageView.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_IMAGE_VIEW`
  VkImageView
);
define_non_dispatchable_handle!(
  /// Khronos: [VkShaderModule](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkShaderModule.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_SHADER_MODULE`
  VkShaderModule
);
define_non_dispatchable_handle!(
  /// Khronos: [VkPipeline](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkPipeline.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_PIPELINE`
  VkPipeline
);
define_non_dispatchable_handle!(
  /// Khronos: [VkPipelineLayout](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkPipelineLayout.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_PIPELINE_LAYOUT`
  VkPipelineLayout
);
define_non_dispatchable_handle!(
  /// Khronos: [VkSampler](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkSampler.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_SAMPLER`
  VkSampler
);
define_non_dispatchable_handle!(
  /// Khronos: [VkDescriptorSet](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDescriptorSet.html) (non-dispatchable handle)
  /// * Parent [VkDescriptorPool]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DESCRIPTOR_SET`
  VkDescriptorSet
);
define_non_dispatchable_handle!(
  /// Khronos: [VkDescriptorSetLayout](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDescriptorSetLayout.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DESCRIPTOR_SET_LAYOUT`
  VkDescriptorSetLayout
);
define_non_dispatchable_handle!(
  /// Khronos: [VkDescriptorPool](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDescriptorPool.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DESCRIPTOR_POOL`
  VkDescriptorPool
);
define_non_dispatchable_handle!(
  /// Khronos: [VkFence](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkFence.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_FENCE`
  VkFence
);
define_non_dispatchable_handle!(
  /// Khronos: [VkSemaphore](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkSemaphore.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_SEMAPHORE`
  VkSemaphore
);
define_non_dispatchable_handle!(
  /// Khronos: [VkEvent](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkEvent.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_EVENT`
  VkEvent
);
define_non_dispatchable_handle!(
  /// Khronos: [VkQueryPool](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkQueryPool.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_QUERY_POOL`
  VkQueryPool
);
define_non_dispatchable_handle!(
  /// Khronos: [VkFramebuffer](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkFramebuffer.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_FRAMEBUFFER`
  VkFramebuffer
);
define_non_dispatchable_handle!(
  /// Khronos: [VkRenderPass](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkRenderPass.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_RENDER_PASS`
  VkRenderPass
);
define_non_dispatchable_handle!(
  /// Khronos: [VkPipelineCache](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkPipelineCache.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_PIPELINE_CACHE`
  VkPipelineCache
);
define_non_dispatchable_handle!(
  /// Khronos: [VkIndirectCommandsLayoutNV](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkIndirectCommandsLayoutNV.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_INDIRECT_COMMANDS_LAYOUT_NV`
  VkIndirectCommandsLayoutNV
);
define_non_dispatchable_handle!(
  /// Khronos: [VkDescriptorUpdateTemplate](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDescriptorUpdateTemplate.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DESCRIPTOR_UPDATE_TEMPLATE`
  VkDescriptorUpdateTemplate
);
define_non_dispatchable_handle!(
  /// Khronos: [VkSamplerYcbcrConversion](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkSamplerYcbcrConversion.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_SAMPLER_YCBCR_CONVERSION`
  VkSamplerYcbcrConversion
);
define_non_dispatchable_handle!(
  /// Khronos: [VkValidationCacheEXT](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkValidationCacheEXT.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_VALIDATION_CACHE_EXT`
  VkValidationCacheEXT
);
define_non_dispatchable_handle!(
  /// Khronos: [VkAccelerationStructureKHR](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkAccelerationStructureKHR.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_ACCELERATION_STRUCTURE_KHR`
  VkAccelerationStructureKHR
);
define_non_dispatchable_handle!(
  /// Khronos: [VkAccelerationStructureNV](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkAccelerationStructureNV.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_ACCELERATION_STRUCTURE_NV`
  VkAccelerationStructureNV
);
define_non_dispatchable_handle!(
  /// Khronos: [VkPerformanceConfigurationINTEL](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkPerformanceConfigurationINTEL.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_PERFORMANCE_CONFIGURATION_INTEL`
  VkPerformanceConfigurationINTEL
);
define_non_dispatchable_handle!(
  /// Khronos: [VkBufferCollectionFUCHSIA](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkBufferCollectionFUCHSIA.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_BUFFER_COLLECTION_FUCHSIA`
  VkBufferCollectionFUCHSIA
);
define_non_dispatchable_handle!(
  /// Khronos: [VkDeferredOperationKHR](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDeferredOperationKHR.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DEFERRED_OPERATION_KHR`
  VkDeferredOperationKHR
);
define_non_dispatchable_handle!(
  /// Khronos: [VkPrivateDataSlot](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkPrivateDataSlot.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_PRIVATE_DATA_SLOT`
  VkPrivateDataSlot
);
define_non_dispatchable_handle!(
  /// Khronos: [VkCuModuleNVX](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkCuModuleNVX.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_CU_MODULE_NVX`
  VkCuModuleNVX
);
define_non_dispatchable_handle!(
  /// Khronos: [VkCuFunctionNVX](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkCuFunctionNVX.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_CU_FUNCTION_NVX`
  VkCuFunctionNVX
);
define_non_dispatchable_handle!(
  /// Khronos: [VkOpticalFlowSessionNV](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkOpticalFlowSessionNV.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_OPTICAL_FLOW_SESSION_NV`
  VkOpticalFlowSessionNV
);
define_non_dispatchable_handle!(
  /// Khronos: [VkMicromapEXT](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkMicromapEXT.html) (non-dispatchable handle)
  /// * Parent [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_MICROMAP_EXT`
  VkMicromapEXT
);

//
// WSI Extensions
//

define_non_dispatchable_handle!(
  /// Khronos: [VkDisplayKHR](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDisplayKHR.html) (non-dispatchable handle)
  /// * Parent: [VkPhysicalDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DISPLAY_KHR`
  VkDisplayKHR
);
define_non_dispatchable_handle!(
  /// Khronos: [VkDisplayModeKHR](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDisplayModeKHR.html) (non-dispatchable handle)
  /// * Parent: [VkDisplayKHR]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DISPLAY_MODE_KHR`
  VkDisplayModeKHR
);
define_non_dispatchable_handle!(
  /// Khronos: [VkSurfaceKHR](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkSurfaceKHR.html) (non-dispatchable handle)
  /// * Parent: [VkInstance]
  /// * Object Type Enum: `VK_OBJECT_TYPE_SURFACE_KHR`
  VkSurfaceKHR
);
define_non_dispatchable_handle!(
  /// Khronos: [VkSwapchainKHR](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkSwapchainKHR.html) (non-dispatchable handle)
  /// * Parent: [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_SWAPCHAIN_KHR`
  VkSwapchainKHR
);
define_non_dispatchable_handle!(
  /// Khronos: [VkDebugReportCallbackEXT](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDebugReportCallbackEXT.html) (non-dispatchable handle)
  /// * Parent: [VkInstance]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DEBUG_REPORT_CALLBACK_EXT`
  VkDebugReportCallbackEXT
);
define_non_dispatchable_handle!(
  /// Khronos: [VkDebugUtilsMessengerEXT](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkDebugUtilsMessengerEXT.html) (non-dispatchable handle)
  /// * Parent: [VkInstance]
  /// * Object Type Enum: `VK_OBJECT_TYPE_DEBUG_UTILS_MESSENGER_EXT`
  VkDebugUtilsMessengerEXT
);

//
// Video extensions
//

define_non_dispatchable_handle!(
  /// Khronos: [VkVideoSessionKHR](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkVideoSessionKHR.html) (non-dispatchable handle)
  /// * Parent: [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_VIDEO_SESSION_KHR`
  VkVideoSessionKHR
);
define_non_dispatchable_handle!(
  /// Khronos: [VkVideoSessionParametersKHR](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkVideoSessionParametersKHR.html) (non-dispatchable handle)
  /// * Parent: [VkVideoSessionKHR]
  /// * Object Type Enum: `VK_OBJECT_TYPE_VIDEO_SESSION_PARAMETERS_KHR`
  VkVideoSessionParametersKHR
);

//
// VK_NV_external_sci_sync2
//

define_non_dispatchable_handle!(
  /// Khronos: [VkSemaphoreSciSyncPoolNV](https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkSemaphoreSciSyncPoolNV.html) (non-dispatchable handle)
  /// * Parent: [VkDevice]
  /// * Object Type Enum: `VK_OBJECT_TYPE_SEMAPHORE_SCI_SYNC_POOL_NV`
  VkSemaphoreSciSyncPoolNV
);

//
// Aliases
//

pub type VkDescriptorUpdateTemplateKHR = VkDescriptorUpdateTemplate;
pub type VkSamplerYcbcrConversionKHR = VkSamplerYcbcrConversion;
pub type VkPrivateDataSlotEXT = VkPrivateDataSlot;
