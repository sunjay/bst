/// The index/ID of a node
///
/// This type is essentially `Option<usize>`. The value usize::MAX is
/// reserved to represent `None`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct NodeIndex(usize);

impl Default for NodeIndex {
    #[inline(always)]
    fn default() -> Self {
        // Default to no node
        NodeIndex(usize::MAX)
    }
}

impl NodeIndex {
    #[inline(always)]
    pub fn new(value: usize) -> Option<Self> {
        if value == usize::MAX {
            None
        } else {
            Some(NodeIndex(value))
        }
    }

    #[inline(always)]
    pub fn into_index(self) -> Option<usize> {
        let NodeIndex(index) = self;
        if index == usize::MAX {
            None
        } else {
            Some(index)
        }
    }

    #[inline(always)]
    pub fn is_none(self) -> bool {
        self.0 == usize::MAX
    }
}
